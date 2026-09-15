import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_192_0 : expNegUpper (355300181472007670769 / 4784759183237377600 : ℝ) ≤ (5638730402844600751294347499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_192_1 : expNegUpper (113831978979808117535311 / 1531122938635960832000 : ℝ) ≤ (2579871811972269522584950369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178751 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_192 : rowCell 0 192 ≤ (196858606946868129331489717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5638730402844600751294347499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2579871811972269522584950369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_192_1
  · norm_num [gridPoint]

theorem exp_0_193_0 : expNegUpper (12717173835990012388431 / 171055240311030272000 : ℝ) ≤ (1289935632963221220304355387 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178751 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_193_1 : expNegUpper (6366205930254176988591 / 85527620155515136000 : ℝ) ≤ (4719978310134342295159158009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (894377 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_193 : rowCell 0 193 ≤ (360219060054701289300398229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1289935632963221220304355387 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4719978310134342295159158009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_193_1
  · norm_num [gridPoint]

theorem exp_0_194_0 : expNegUpper (2304334764865111029679 / 30957884505366784000 : ℝ) ≤ (4719977321945942393938145529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (894377 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_194_1 : expNegUpper (4614204204263983444077 / 61915769010733568000 : ℝ) ≤ (4316364979985136115670968389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (447501 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_194 : rowCell 0 194 ≤ (82367274905700142015505633 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4719977321945942393938145529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4316364979985136115670968389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_194_1
  · norm_num [gridPoint]

theorem exp_0_195_0 : expNegUpper (115982589221417421339357 / 1556314126043161088000 : ℝ) ≤ (4316364086063306551417509779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (447501 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_195_1 : expNegUpper (29030546014554991296559 / 389078531510790272000 : ℝ) ≤ (789211992741982478747160379 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (895629 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_195 : rowCell 0 195 ≤ (150625846245267585901743881 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4316364086063306551417509779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (789211992741982478747160379 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_195_1
  · norm_num [gridPoint]

theorem exp_0_196_0 : expNegUpper (3243114651409287994199 / 43465468475659392000 : ℝ) ≤ (986514788821347902169220739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (895629 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_196_1 : expNegUpper (2597621190928332661703 / 34772374780527513600 : ℝ) ≤ (450803884635936636458976887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_196 : rowCell 0 196 ≤ (68841796648134237482878129 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (986514788821347902169220739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (450803884635936636458976887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_196_1
  · norm_num [gridPoint]

theorem exp_0_197_0 : expNegUpper (23505072584709007513687 / 314644488502014054400 : ℝ) ≤ (721286069236623797508269997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (896259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_197_1 : expNegUpper (58833711849801623301093 / 786611221255035136000 : ℝ) ≤ (3295043035780782167178524157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_197 : rowCell 0 197 ≤ (503261639555299280394616917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (721286069236623797508269997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3295043035780782167178524157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_197_1
  · norm_num [gridPoint]

theorem exp_0_198_0 : expNegUpper (59151152816094038700117 / 790855429101078784000 : ℝ) ≤ (3295042375142425142222952477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1793783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_198_1 : expNegUpper (118445604374043442391953 / 1581710858202157568000 : ℝ) ≤ (3009643769625993332708903601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1795053 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_198 : rowCell 0 198 ≤ (459743378042971265568004517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3295042375142425142222952477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3009643769625993332708903601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_198_1
  · norm_num [gridPoint]

theorem exp_0_199_0 : expNegUpper (846812199601792953 / 11308246131200000 : ℝ) ≤ (1504821586329627379198368827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1795053 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_199_1 : expNegUpper (105980004984385959 / 1413530766400000 : ℝ) ≤ (274815159119435090774003169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_199 : rowCell 0 199 ≤ (419863567198938074898533891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1504821586329627379198368827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (274815159119435090774003169 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_199_1
  · norm_num [gridPoint]

theorem exp_0_200_0 : expNegUpper (14983419090790731767959 / 199844525562949696000 : ℝ) ≤ (1374075525953286027300581521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_200_1 : expNegUpper (120013137392114177780391 / 1598756204503597568000 : ℝ) ≤ (1254321587154467786815338987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_200 : rowCell 0 200 ≤ (383330157876697431745800587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1374075525953286027300581521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1254321587154467786815338987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_200_1
  · norm_num [gridPoint]

theorem exp_0_201_0 : expNegUpper (120655477096497884513439 / 1607313135112950272000 : ℝ) ≤ (501728537451219047306015467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1797609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_201_1 : expNegUpper (12080250972042201083719 / 160731313511295027200 : ℝ) ≤ (2289342299639428326847526077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899447 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_201 : rowCell 0 201 ≤ (349873375934058242188446313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (501728537451219047306015467 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2289342299639428326847526077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_201_1
  · norm_num [gridPoint]

theorem exp_0_202_0 : expNegUpper (1349414985242854131711 / 17954365600311756800 : ℝ) ≤ (2289341859877538481797251577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (899447 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_202_1 : expNegUpper (13510625842744038863829 / 179543656003117568000 : ℝ) ≤ (1044304662990879743787815169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225023 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_202 : rowCell 0 202 ≤ (79811033447094638347422477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2289341859877538481797251577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1044304662990879743787815169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_202_1
  · norm_num [gridPoint]

theorem exp_0_203_0 : expNegUpper (122242977444741462894389 / 1624495511248921088000 : ℝ) ≤ (417721785804479469519727241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225023 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_203_1 : expNegUpper (30598128994318960330317 / 406123877812230272000 : ℝ) ≤ (1904931347344862549084323641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_203 : rowCell 0 203 ≤ (291212544899042640376184859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (417721785804479469519727241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1904931347344862549084323641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_203_1
  · norm_num [gridPoint]

theorem exp_0_204_0 : expNegUpper (1230423734074903043637 / 16331209567755392000 : ℝ) ≤ (7619723956458017941708941 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1801479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_204_1 : expNegUpper (4927726795619965288267 / 65324838271021568000 : ℝ) ≤ (43422824937525922848558081 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_204 : rowCell 0 204 ≤ (132783267736606001871252101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7619723956458017941708941 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43422824937525922848558081 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_204_1
  · norm_num [gridPoint]

theorem exp_0_205_0 : expNegUpper (443890847858215207853 / 5884477564902912000 : ℝ) ≤ (434228168575971244408809521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_205_1 : expNegUpper (222217928882983636487 / 2942238782451456000 : ℝ) ≤ (791633932599660253893215007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_205 : rowCell 0 205 ≤ (242110547915277203908126347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (434228168575971244408809521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (791633932599660253893215007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_205_1
  · norm_num [gridPoint]

theorem exp_0_206_0 : expNegUpper (62326253435967662752657 / 825220181373020416000 : ℝ) ≤ (791633786841667914127383039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_206_1 : expNegUpper (24961165849646339781909 / 330088072549208166400 : ℝ) ≤ (1442810484783460989536914789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_206 : rowCell 0 206 ≤ (110332165382702238858067677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (791633786841667914127383039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1442810484783460989536914789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_206_1
  · norm_num [gridPoint]

theorem exp_0_207_0 : expNegUpper (25092652871661759727149 / 331826864637984870400 : ℝ) ≤ (721405110954670120569378761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_207_1 : expNegUpper (7851115917338641761571 / 103695895199370272000 : ℝ) ≤ (657224434244689012773892457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451677 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_207 : rowCell 0 207 ≤ (201061810096838566105225401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (721405110954670120569378761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (657224434244689012773892457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_207_1
  · norm_num [gridPoint]

theorem exp_0_208_0 : expNegUpper (876929368082646591051 / 11582299457913632000 : ℝ) ≤ (1314448631502229535231145623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451677 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_208_1 : expNegUpper (14048187844067024857287 / 185316791326618112000 : ℝ) ≤ (37411798381696717387994853 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452007 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_208 : rowCell 0 208 ≤ (183150037564074804995870813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1314448631502229535231145623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37411798381696717387994853 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_208_1
  · norm_num [gridPoint]

theorem exp_0_209_0 : expNegUpper (5083848432042036146447 / 67063630359798272000 : ℝ) ≤ (7482358341361187300013781 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452007 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_209_1 : expNegUpper (2545066939962504244599 / 33531815179899136000 : ℝ) ≤ (1090071096044810388190268663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226169 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_209 : rowCell 0 209 ≤ (83394105256839370701781347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7482358341361187300013781 / 6250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1090071096044810388190268663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_209_1
  · norm_num [gridPoint]

theorem exp_0_210_0 : expNegUpper (63959209871048414507151 / 842676617178052864000 : ℝ) ≤ (1090070903577602589028907387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226169 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_210_1 : expNegUpper (128076833874322880457301 / 1685353234356105728000 : ℝ) ≤ (992278094298782168226902799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (905341 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_210 : rowCell 0 210 ≤ (75923379892786878031762013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1090070903577602589028907387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (992278094298782168226902799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_210_1
  · norm_num [gridPoint]

theorem exp_0_211_0 : expNegUpper (14304940646597503544421 / 188237616447001088000 : ℝ) ≤ (198455584182600981228395173 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (905341 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_211_1 : expNegUpper (143226845797260972363 / 1882376164470010880 : ℝ) ≤ (451507763635757635356269571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362403 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_211 : rowCell 0 211 ≤ (34551625261080641144019407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (198455584182600981228395173 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (451507763635757635356269571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_211_1
  · norm_num [gridPoint]

theorem exp_0_212_0 : expNegUpper (1295743590252316590467 / 17029466999956689920 : ℝ) ≤ (112876921389147627923081981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362403 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_212_1 : expNegUpper (129735339020099842967211 / 1702946699995668992000 : ℝ) ≤ (51347723017288847135314221 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_212 : rowCell 0 212 ≤ (6287892284334763099033809 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112876921389147627923081981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51347723017288847135314221 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_212_1
  · norm_num [gridPoint]

theorem exp_0_213_0 : expNegUpper (130408109351997857184099 / 1711777690274083328000 : ℝ) ≤ (164312685533552447115056783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (906677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_213_1 : expNegUpper (65285188637178215353949 / 855888845137041664000 : ℝ) ≤ (747260736932958977819195029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907349 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_213 : rowCell 0 213 ≤ (28600016893286243585297641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (164312685533552447115056783 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (747260736932958977819195029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_213_1
  · norm_num [gridPoint]

theorem exp_0_214_0 : expNegUpper (291657170648921717869 / 3823625597462784000 : ℝ) ≤ (747260610355358649541255927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907349 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_214_1 : expNegUpper (584041270989525711457 / 7647251194925568000 : ℝ) ≤ (679499402968768769890125009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908023 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_214 : rowCell 0 214 ≤ (52020311013147421160332347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (747260610355358649541255927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (679499402968768769890125009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_214_1
  · norm_num [gridPoint]

theorem exp_0_215_0 : expNegUpper (132087221337621053346617 / 1729508185748177408000 : ℝ) ≤ (33974964452457616874963661 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908023 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_215_1 : expNegUpper (16531509388412381600757 / 216188523218522176000 : ℝ) ≤ (617721614090562211376632039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_215 : rowCell 0 215 ≤ (47297256864426574745660509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33974964452457616874963661 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (617721614090562211376632039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_215_1
  · norm_num [gridPoint]

theorem exp_0_216_0 : expNegUpper (16616575372644418103733 / 217300961367982144000 : ℝ) ≤ (308860755793557396523905201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_216_1 : expNegUpper (26619750934132476124331 / 347681538188771430400 : ℝ) ≤ (280707613348001229841160241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454689 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_216 : rowCell 0 216 ≤ (42991855168134105653618947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (308860755793557396523905201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (280707613348001229841160241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_216_1
  · norm_num [gridPoint]

theorem exp_0_217_0 : expNegUpper (2972930704776806538219 / 38829556321006489600 : ℝ) ≤ (561415134486104376603784977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454689 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_217_1 : expNegUpper (7441629703059550847427 / 97073890802516224000 : ℝ) ≤ (10202206387919101274279869 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910059 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_217 : rowCell 0 217 ≤ (39068299397864873275375407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (561415134486104376603784977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10202206387919101274279869 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_217_1
  · norm_num [gridPoint]

theorem exp_0_218_0 : expNegUpper (67317533765681274122827 / 878137608126241024000 : ℝ) ≤ (255055118232513439114040211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910059 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_218_1 : expNegUpper (134803825052866303431213 / 1756275216252482048000 : ℝ) ≤ (463375870450404803494582351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364297 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_218 : rowCell 0 218 ≤ (35493740766348730032184059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (255055118232513439114040211 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (463375870450404803494582351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_218_1
  · norm_num [gridPoint]

theorem exp_0_219_0 : expNegUpper (5419686816908510145453 / 70609729454617088000 : ℝ) ≤ (463375795881765575534570563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364297 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_219_1 : expNegUpper (1356622358563841918833 / 17652432363654272000 : ℝ) ≤ (420816681315760307621575401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_219 : rowCell 0 219 ≤ (16119027457230579887976703 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (463375795881765575534570563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (420816681315760307621575401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_219_1
  · norm_num [gridPoint]

theorem exp_0_220_0 : expNegUpper (3787588899481821031137 / 49284280410670208000 : ℝ) ≤ (420816614281410304471649361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_220_1 : expNegUpper (15169397450884914148779 / 197137121642680832000 : ℝ) ≤ (38207052954719722608439621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824233 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_220 : rowCell 0 220 ≤ (58547251871900344642725077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (420816614281410304471649361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38207052954719722608439621 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_220_1
  · norm_num [gridPoint]

theorem exp_0_221_0 : expNegUpper (137218167399599605428539 / 1783247791508582912000 : ℝ) ≤ (382070469299443753088089097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824233 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_221_1 : expNegUpper (13739085864994505652741 / 178324779150858291200 : ℝ) ≤ (346805535299394844013765639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_221 : rowCell 0 221 ≤ (13287573276220673067429833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (382070469299443753088089097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (346805535299394844013765639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_221_1
  · norm_num [gridPoint]

theorem exp_0_222_0 : expNegUpper (13808708146981354528821 / 179228432653879347200 : ℝ) ≤ (346805481163246709975401029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_222_1 : expNegUpper (138261090624665326177561 / 1792284326538793472000 : ℝ) ≤ (157358863311398973659511801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_222 : rowCell 0 222 ≤ (48238866649015371684406233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (346805481163246709975401029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (157358863311398973659511801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_222_1
  · norm_num [gridPoint]

theorem exp_0_223_0 : expNegUpper (15439994731591780381001 / 200149299986084352000 : ℝ) ≤ (157358838994530190266880179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_223_1 : expNegUpper (483108621439110010481 / 6254665624565136000 : ℝ) ≤ (142764394830540184542088183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828389 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_223 : rowCell 0 223 ≤ (43770511704984042885469681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (157358838994530190266880179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (142764394830540184542088183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_223_1
  · norm_num [gridPoint]

theorem sum_0_192_2 : blockSum (rowCell 0) 192 2 ≤ (753936273948437547963377663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_192) (by simpa only [blockSum_one] using cell_0_193) (by norm_num)

theorem sum_0_194_2 : blockSum (rowCell 0) 194 2 ≤ (315360396056667869932755147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_194) (by simpa only [blockSum_one] using cell_0_195) (by norm_num)

theorem sum_0_192_4 : blockSum (rowCell 0) 192 4 ≤ (1384657066061773287828887957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_192_2 sum_0_194_2 (by norm_num)

theorem sum_0_196_2 : blockSum (rowCell 0) 196 2 ≤ (1053996012740373180257641949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_196) (by simpa only [blockSum_one] using cell_0_197) (by norm_num)

theorem sum_0_198_2 : blockSum (rowCell 0) 198 2 ≤ (109950868155238667558317301 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_198) (by simpa only [blockSum_one] using cell_0_199) (by norm_num)

theorem sum_0_196_4 : blockSum (rowCell 0) 196 4 ≤ (1933602957982282520724180357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_196_2 sum_0_198_2 (by norm_num)

theorem sum_0_192_8 : blockSum (rowCell 0) 192 8 ≤ (4702917090105829096381956271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_192_4 sum_0_196_4 (by norm_num)

theorem sum_0_200_2 : blockSum (rowCell 0) 200 2 ≤ (7332035338107556739342469 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_200) (by simpa only [blockSum_one] using cell_0_201) (by norm_num)

theorem sum_0_202_2 : blockSum (rowCell 0) 202 2 ≤ (610456678687421193765874767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_202) (by simpa only [blockSum_one] using cell_0_203) (by norm_num)

theorem sum_0_200_4 : blockSum (rowCell 0) 200 4 ≤ (1343660212498176867700121667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_200_2 sum_0_202_2 (by norm_num)

theorem sum_0_204_2 : blockSum (rowCell 0) 204 2 ≤ (507677083388489207650630549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_204) (by simpa only [blockSum_one] using cell_0_205) (by norm_num)

theorem sum_0_206_2 : blockSum (rowCell 0) 206 2 ≤ (84345228172448608764272151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_206) (by simpa only [blockSum_one] using cell_0_207) (by norm_num)

theorem sum_0_204_4 : blockSum (rowCell 0) 204 4 ≤ (116175403031341531433998913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_204_2 sum_0_206_2 (by norm_num)

theorem sum_0_200_8 : blockSum (rowCell 0) 200 8 ≤ (2273063436748909119172112971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_200_4 sum_0_204_4 (by norm_num)

theorem sum_0_192_16 : blockSum (rowCell 0) 192 16 ≤ (3487990263427369107777034621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_192_8 sum_0_200_8 (by norm_num)

theorem sum_0_208_2 : blockSum (rowCell 0) 208 2 ≤ (349938248077753546399433507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_208) (by simpa only [blockSum_one] using cell_0_209) (by norm_num)

theorem sum_0_210_2 : blockSum (rowCell 0) 210 2 ≤ (145026630414948160319800827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_210) (by simpa only [blockSum_one] using cell_0_211) (by norm_num)

theorem sum_0_208_4 : blockSum (rowCell 0) 208 4 ≤ (639991508907649867039035161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_208_2 sum_0_210_2 (by norm_num)

theorem sum_0_212_2 : blockSum (rowCell 0) 212 2 ≤ (30019739157480029540233343 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_212) (by simpa only [blockSum_one] using cell_0_213) (by norm_num)

theorem sum_0_214_2 : blockSum (rowCell 0) 214 2 ≤ (12414695984696749488249107 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_214) (by simpa only [blockSum_one] using cell_0_215) (by norm_num)

theorem sum_0_212_4 : blockSum (rowCell 0) 212 4 ≤ (54849131126873528516731557 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_212_2 sum_0_214_2 (by norm_num)

theorem sum_0_208_8 : blockSum (rowCell 0) 208 8 ≤ (1078784557922638095172887617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_208_4 sum_0_212_4 (by norm_num)

theorem sum_0_216_2 : blockSum (rowCell 0) 216 2 ≤ (41030077282999489464497177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_216) (by simpa only [blockSum_one] using cell_0_217) (by norm_num)

theorem sum_0_218_2 : blockSum (rowCell 0) 218 2 ≤ (13546359136161977961627493 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_218) (by simpa only [blockSum_one] using cell_0_219) (by norm_num)

theorem sum_0_216_4 : blockSum (rowCell 0) 216 4 ≤ (149791950246808868737131819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_216_2 sum_0_218_2 (by norm_num)

theorem sum_0_220_2 : blockSum (rowCell 0) 220 2 ≤ (111697544976783036912444409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_220) (by simpa only [blockSum_one] using cell_0_221) (by norm_num)

theorem sum_0_222_2 : blockSum (rowCell 0) 222 2 ≤ (46004689176999707284937957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_222) (by simpa only [blockSum_one] using cell_0_223) (by norm_num)

theorem sum_0_220_4 : blockSum (rowCell 0) 220 4 ≤ (203706923330782451482320323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_220_2 sum_0_222_2 (by norm_num)

theorem sum_0_216_8 : blockSum (rowCell 0) 216 8 ≤ (503290823824400188956583961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_216_4 sum_0_220_4 (by norm_num)

theorem sum_0_208_16 : blockSum (rowCell 0) 208 16 ≤ (791037690873519142064735789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_208_8 sum_0_216_8 (by norm_num)

theorem sum_0_192_32 : blockSum (rowCell 0) 192 32 ≤ (427902795430088824984177041 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_192_16 sum_0_208_16 (by norm_num)

#print axioms sum_0_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
