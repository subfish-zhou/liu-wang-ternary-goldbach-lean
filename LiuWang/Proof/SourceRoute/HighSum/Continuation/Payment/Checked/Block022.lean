import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_192_0 : expNegUpper (363644013451630070769 / 4784759183237377600 : ℝ) ≤ (123240455367868499397145299 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452693 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_192_1 : expNegUpper (116494723478967157535311 / 1531122938635960832000 : ℝ) ≤ (906474302742605633691045841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1811961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_192 : rowCell 1 192 ≤ (137995358400669897481658181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (123240455367868499397145299 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (906474302742605633691045841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_192_1
  · norm_num [gridPoint]

theorem exp_1_193_0 : expNegUpper (39043957497236469165293 / 513165720933090816000 : ℝ) ≤ (906474094893306423144672083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1811961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_193_1 : expNegUpper (19543622163009058965773 / 256582860466545408000 : ℝ) ≤ (833146851544350898727865091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453289 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_193 : rowCell 1 193 ≤ (126854722354928036993695531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (906474094893306423144672083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (833146851544350898727865091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_193_1
  · norm_num [gridPoint]

theorem exp_1_194_0 : expNegUpper (2358026558907499509679 / 30957884505366784000 : ℝ) ≤ (41657333128923235434408609 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453289 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_194_1 : expNegUpper (4721296522975955284077 / 61915769010733568000 : ℝ) ≤ (153099138752056799033496667 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453589 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_194 : rowCell 1 194 ≤ (116574436904463578579693021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41657333128923235434408609 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (153099138752056799033496667 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_194_1
  · norm_num [gridPoint]

theorem exp_1_195_0 : expNegUpper (118674460657856973339357 / 1556314126043161088000 : ℝ) ≤ (765495522014439813533393791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453589 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_195_1 : expNegUpper (29701693440084847296559 / 389078531510790272000 : ℝ) ≤ (87888139105286447289596861 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_195 : rowCell 1 195 ≤ (53545838869817866094162083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (765495522014439813533393791 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87888139105286447289596861 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_195_1
  · norm_num [gridPoint]

theorem exp_1_196_0 : expNegUpper (9954273385124503982597 / 130396405426978176000 : ℝ) ≤ (140620991358861968407553399 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_196_1 : expNegUpper (7972321668547634785109 / 104317124341582540800 : ℝ) ≤ (80698459760769276114343739 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_196 : rowCell 1 196 ≤ (98347878651522589012378311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (140620991358861968407553399 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80698459760769276114343739 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_196_1
  · norm_num [gridPoint]

theorem exp_1_197_0 : expNegUpper (24046359565724969113687 / 314644488502014054400 : ℝ) ≤ (645587536343598382193399411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_197_1 : expNegUpper (60183288435181463301093 / 786611221255035136000 : ℝ) ≤ (592582514245807869658957781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_197 : rowCell 1 197 ≤ (45144236253692165152376643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (645587536343598382193399411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (592582514245807869658957781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_197_1
  · norm_num [gridPoint]

theorem exp_1_198_0 : expNegUpper (60508011135794006700117 / 790855429101078784000 : ℝ) ≤ (148145596383852766445394603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_198_1 : expNegUpper (121152039279123250391953 / 1581710858202157568000 : ℝ) ≤ (135938414910951913591276293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181921 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_198 : rowCell 1 198 ≤ (82862645341384219777415049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148145596383852766445394603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (135938414910951913591276293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_198_1
  · norm_num [gridPoint]

theorem exp_1_199_0 : expNegUpper (2598484564111406891 / 33924738393600000 : ℝ) ≤ (543753542801712644028057131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181921 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_199_1 : expNegUpper (325176592658224373 / 4240592299200000 : ℝ) ≤ (99757701966344720101745977 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_199 : rowCell 1 199 ≤ (76023103136905583804498461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (543753542801712644028057131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99757701966344720101745977 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_199_1
  · norm_num [gridPoint]

theorem exp_1_200_0 : expNegUpper (1178804161868904289843 / 15372655812534592000 : ℝ) ≤ (62348550474309798013803007 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910219 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_200_1 : expNegUpper (9441087366602633983107 / 122981246500276736000 : ℝ) ≤ (91479268759039168732690443 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_200 : rowCell 1 200 ≤ (34862925433236603643605037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62348550474309798013803007 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (91479268759039168732690443 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_200_1
  · norm_num [gridPoint]

theorem exp_1_201_0 : expNegUpper (123391038938858204513439 / 1607313135112950272000 : ℝ) ≤ (457396247591450611344231799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_201_1 : expNegUpper (12353078982846220283719 / 160731313511295027200 : ℝ) ≤ (419306929660690583601060891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455727 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_201 : rowCell 1 201 ≤ (63929983348236948406015577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (457396247591450611344231799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (419306929660690583601060891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_201_1
  · norm_num [gridPoint]

theorem exp_1_202_0 : expNegUpper (4139673074951243995133 / 53863096800935270400 : ℝ) ≤ (419306842403545348897416881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455727 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_202_1 : expNegUpper (41443731475685556591487 / 538630968009352704000 : ℝ) ≤ (96067301710608604356560353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824151 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_202 : rowCell 1 202 ≤ (5859748747387358899526747 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (419306842403545348897416881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96067301710608604356560353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_202_1
  · norm_num [gridPoint]

theorem exp_1_203_0 : expNegUpper (124993102755742038894389 / 1624495511248921088000 : ℝ) ≤ (192134563861194946434707499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824151 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_203_1 : expNegUpper (31283839888489072330317 / 406123877812230272000 : ℝ) ≤ (1408200166266017690100301 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_203 : rowCell 1 203 ≤ (53693055361299831469552717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (192134563861194946434707499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1408200166266017690100301 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_203_1
  · norm_num [gridPoint]

theorem exp_1_204_0 : expNegUpper (1257997804528110083637 / 16331209567755392000 : ℝ) ≤ (3520499698449718134113897 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825399 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_204_1 : expNegUpper (5037731808059988328267 / 65324838271021568000 : ℝ) ≤ (161216526361345909547446731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_204 : rowCell 1 204 ≤ (49183907986474620217652999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3520499698449718134113897 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (161216526361345909547446731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_204_1
  · norm_num [gridPoint]

theorem exp_1_205_0 : expNegUpper (1361400379914869623559 / 17653432694708736000 : ℝ) ≤ (6448659754520403007992589 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_205_1 : expNegUpper (681478555709814909461 / 8826716347354368000 : ℝ) ≤ (73804376255436656092961471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228489 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_205 : rowCell 1 205 ≤ (45039628851531731288047691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6448659754520403007992589 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73804376255436656092961471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_205_1
  · norm_num [gridPoint]

theorem exp_1_206_0 : expNegUpper (63712238692948142752657 / 825220181373020416000 : ℝ) ≤ (295217446135728991063625057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228489 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_206_1 : expNegUpper (25514103605574506181909 / 330088072549208166400 : ℝ) ≤ (270217266474285835970150043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228647 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_206 : rowCell 1 206 ≤ (10308001812817972936874761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (295217446135728991063625057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (270217266474285835970150043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_206_1
  · norm_num [gridPoint]

theorem exp_1_207_0 : expNegUpper (25648503321317977327149 / 331826864637984870400 : ℝ) ≤ (33777151642388573088920649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228647 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_207_1 : expNegUpper (8024364074461201761571 / 103695895199370272000 : ℝ) ≤ (247259827256468411988593593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366089 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_207 : rowCell 1 207 ≤ (4716861338302994375071121 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33777151642388573088920649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (247259827256468411988593593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_207_1
  · norm_num [gridPoint]

theorem exp_1_208_0 : expNegUpper (2688840895552131773153 / 34746898373740896000 : ℝ) ≤ (49451955792413945685681909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366089 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_208_1 : expNegUpper (43070980948294770571861 / 555950373979854336000 : ℝ) ≤ (226185377085085751807576907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45793 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_208 : rowCell 1 208 ≤ (34524046139840963735059907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49451955792413945685681909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (226185377085085751807576907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_208_1
  · norm_num [gridPoint]

theorem exp_1_209_0 : expNegUpper (5195601060718889906447 / 67063630359798272000 : ℝ) ≤ (11309266668344622426342881 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45793 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_209_1 : expNegUpper (2600797619614528564599 / 33531815179899136000 : ℝ) ≤ (103422969144839877551687059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_209 : rowCell 1 209 ≤ (15788514690365187020152849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11309266668344622426342881 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (103422969144839877551687059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_209_1
  · norm_num [gridPoint]

theorem exp_1_210_0 : expNegUpper (65359758596669150507151 / 842676617178052864000 : ℝ) ≤ (51711474681173309234073219 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_210_1 : expNegUpper (130870649591244224457301 / 1685353234356105728000 : ℝ) ≤ (94552275920242041278102979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458571 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_210 : rowCell 1 210 ≤ (28873062591945659788890997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51711474681173309234073219 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (94552275920242041278102979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_210_1
  · norm_num [gridPoint]

theorem exp_1_211_0 : expNegUpper (43850948334979710633263 / 564712849341003264000 : ℝ) ≤ (94552258021844257335127867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458571 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_211_1 : expNegUpper (439017528895921157089 / 5647128493410032640 : ℝ) ≤ (34566902733458784472256051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917787 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_211 : rowCell 1 211 ≤ (211143353808974762152983 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (94552258021844257335127867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34566902733458784472256051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_211_1
  · norm_num [gridPoint]

theorem exp_1_212_0 : expNegUpper (1323900199451133870467 / 17029466999956689920 : ℝ) ≤ (172834481288361548265767407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917787 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_212_1 : expNegUpper (132543718205661442967211 / 1702946699995668992000 : ℝ) ≤ (157918658684809705628117667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459217 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_212 : rowCell 1 212 ≤ (602970403196696061999763 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172834481288361548265767407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (157918658684809705628117667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_212_1
  · norm_num [gridPoint]

theorem exp_1_213_0 : expNegUpper (10248542462015362552623 / 131675206944160256000 : ℝ) ≤ (157918629405080063269439893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459217 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_213_1 : expNegUpper (5130232238239929181073 / 65837603472080128000 : ℝ) ≤ (144248690023668093541484513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229771 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_213 : rowCell 1 213 ≤ (22034312411195364860574743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (157918629405080063269439893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (144248690023668093541484513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_213_1
  · norm_num [gridPoint]

theorem exp_1_214_0 : expNegUpper (893839674536911713607 / 11470876792388352000 : ℝ) ≤ (18031082944172445475129693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229771 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_214_1 : expNegUpper (1789763048357935214371 / 22941753584776704000 : ℝ) ≤ (131724551052454028464502397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_214 : rowCell 1 214 ≤ (2515526844217797872077653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18031082944172445475129693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (131724551052454028464502397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_214_1
  · norm_num [gridPoint]

theorem exp_1_215_0 : expNegUpper (134924727460463165346617 / 1729508185748177408000 : ℝ) ≤ (65862263564103863774562453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839473 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_215_1 : expNegUpper (16885287436977629600757 / 216188523218522176000 : ℝ) ≤ (120253837863747772619475241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_215 : rowCell 1 215 ≤ (9187244381012846266157003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65862263564103863774562453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (120253837863747772619475241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_215_1
  · norm_num [gridPoint]

theorem exp_1_216_0 : expNegUpper (16972173854789698103733 / 217300961367982144000 : ℝ) ≤ (60126908123092636865199153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_216_1 : expNegUpper (27187252158700898524331 / 347681538188771430400 : ℝ) ≤ (109751249986044690669538657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_216 : rowCell 1 216 ≤ (4193044018707725505788011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60126908123092636865199153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109751249986044690669538657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_216_1
  · norm_num [gridPoint]

theorem exp_1_217_0 : expNegUpper (9108930087095910814657 / 116488668963019468800 : ℝ) ≤ (109751230457722436501634021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_217_1 : expNegUpper (22799020418705692542281 / 291221672407548672000 : ℝ) ≤ (100138077172608928738536873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_217 : rowCell 1 217 ≤ (765265844241429363957461 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109751230457722436501634021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100138077172608928738536873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_217_1
  · norm_num [gridPoint]

theorem exp_1_218_0 : expNegUpper (68747209428582522122827 / 878137608126241024000 : ℝ) ≤ (10013805953605348017451003 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_218_1 : expNegUpper (137655894644348671431213 / 1756275216252482048000 : ℝ) ≤ (91341720207467783191122259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_218 : rowCell 1 218 ≤ (6981438785756091922253481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10013805953605348017451003 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (91341720207467783191122259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_218_1
  · norm_num [gridPoint]

theorem exp_1_219_0 : expNegUpper (5534352139313415105453 / 70609729454617088000 : ℝ) ≤ (91341704283397246211861591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (922371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_219_1 : expNegUpper (1385215871821866878833 / 17652432363654272000 : ℝ) ≤ (8329524375736609217408687 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_219 : rowCell 1 219 ≤ (12734683151515468008415193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91341704283397246211861591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8329524375736609217408687 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_219_1
  · norm_num [gridPoint]

theorem exp_1_220_0 : expNegUpper (11602259597982359093411 / 147852841232010624000 : ℝ) ≤ (16659045876612835903048909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_220_1 : expNegUpper (46463736706028950446337 / 591411364928042496000 : ℝ) ≤ (75936959386181378868675679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_220 : rowCell 1 220 ≤ (725709641576436467900739 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16659045876612835903048909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75936959386181378868675679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_220_1
  · norm_num [gridPoint]

theorem exp_1_221_0 : expNegUpper (140099363928362485428539 / 1783247791508582912000 : ℝ) ≤ (37968473207005800064936847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923703 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_221_1 : expNegUpper (14026477344438780852741 / 178324779150858291200 : ℝ) ≤ (69210036934705505742432887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369749 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_221 : rowCell 1 221 ≤ (2646062107820325930808351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37968473207005800064936847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69210036934705505742432887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_221_1
  · norm_num [gridPoint]

theorem exp_1_222_0 : expNegUpper (14097555973289655328821 / 179228432653879347200 : ℝ) ≤ (34605012615376972058802009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369749 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_222_1 : expNegUpper (141142287153428206177561 / 1792284326538793472000 : ℝ) ≤ (31531071276765288895014891 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_222 : rowCell 1 222 ≤ (9645405313105771030629809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34605012615376972058802009 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31531071276765288895014891 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_222_1
  · norm_num [gridPoint]

theorem exp_1_223_0 : expNegUpper (47285237527243053143003 / 600447899958253056000 : ℝ) ≤ (31531065998183303877596249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850089 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_223_1 : expNegUpper (1479414179557778031443 / 18763996873695408000 : ℝ) ≤ (57445101759783528802565899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925719 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_223 : rowCell 1 223 ≤ (1098436969214536968616257 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31531065998183303877596249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57445101759783528802565899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_223_1
  · norm_num [gridPoint]

theorem sum_1_192_2 : blockSum (rowCell 1) 192 2 ≤ (16553130047224870904709607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_192) (by simpa only [blockSum_one] using cell_1_193) (by norm_num)

theorem sum_1_194_2 : blockSum (rowCell 1) 194 2 ≤ (223666114644099310768017187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_194) (by simpa only [blockSum_one] using cell_1_195) (by norm_num)

theorem sum_1_192_4 : blockSum (rowCell 1) 192 4 ≤ (488516195399697245243370899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_192_2 sum_1_194_2 (by norm_num)

theorem sum_1_196_2 : blockSum (rowCell 1) 196 2 ≤ (188636351158906919317131597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_196) (by simpa only [blockSum_one] using cell_1_197) (by norm_num)

theorem sum_1_198_2 : blockSum (rowCell 1) 198 2 ≤ (15888574847828980358191351 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_198) (by simpa only [blockSum_one] using cell_1_199) (by norm_num)

theorem sum_1_196_4 : blockSum (rowCell 1) 196 4 ≤ (347522099637196722899045107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_196_2 sum_1_198_2 (by norm_num)

theorem sum_1_192_8 : blockSum (rowCell 1) 192 8 ≤ (418019147518446984071208003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_192_4 sum_1_196_4 (by norm_num)

theorem sum_1_200_2 : blockSum (rowCell 1) 200 2 ≤ (133655834214710155693225651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_200) (by simpa only [blockSum_one] using cell_1_201) (by norm_num)

theorem sum_1_202_2 : blockSum (rowCell 1) 202 2 ≤ (112290542835173420464820187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_202) (by simpa only [blockSum_one] using cell_1_203) (by norm_num)

theorem sum_1_200_4 : blockSum (rowCell 1) 200 4 ≤ (122973188524941788079022919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_200_2 sum_1_202_2 (by norm_num)

theorem sum_1_204_2 : blockSum (rowCell 1) 204 2 ≤ (9422353683800635150570069 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_204) (by simpa only [blockSum_one] using cell_1_205) (by norm_num)

theorem sum_1_206_2 : blockSum (rowCell 1) 206 2 ≤ (19741724489423961687017003 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_206) (by simpa only [blockSum_one] using cell_1_207) (by norm_num)

theorem sum_1_204_4 : blockSum (rowCell 1) 204 4 ≤ (86595217397851099126884351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_204_2 sum_1_206_2 (by norm_num)

theorem sum_1_200_8 : blockSum (rowCell 1) 200 8 ≤ (20956840592279288720590727 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_200_4 sum_1_204_4 (by norm_num)

theorem sum_1_192_16 : blockSum (rowCell 1) 192 16 ≤ (627587553441239871277115273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_192_8 sum_1_200_8 (by norm_num)

theorem sum_1_208_2 : blockSum (rowCell 1) 208 2 ≤ (13220215104114267555073121 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_208) (by simpa only [blockSum_one] using cell_1_209) (by norm_num)

theorem sum_1_210_2 : blockSum (rowCell 1) 210 2 ≤ (3454123863629219066125867 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_210) (by simpa only [blockSum_one] using cell_1_211) (by norm_num)

theorem sum_1_208_4 : blockSum (rowCell 1) 208 4 ≤ (121367057338638842833379477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_208_2 sum_1_210_2 (by norm_num)

theorem sum_1_212_2 : blockSum (rowCell 1) 212 2 ≤ (46153128539063207340565263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_212) (by simpa only [blockSum_one] using cell_1_213) (by norm_num)

theorem sum_1_214_2 : blockSum (rowCell 1) 214 2 ≤ (3849870351576807550893523 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_214) (by simpa only [blockSum_one] using cell_1_215) (by norm_num)

theorem sum_1_212_4 : blockSum (rowCell 1) 212 4 ≤ (84651832054831282849500493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_212_2 sum_1_214_2 (by norm_num)

theorem sum_1_208_8 : blockSum (rowCell 1) 208 8 ≤ (20601888939347012568287997 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_208_4 sum_1_212_4 (by norm_num)

theorem sum_1_216_2 : blockSum (rowCell 1) 216 2 ≤ (2004843309978718081393829 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_216) (by simpa only [blockSum_one] using cell_1_217) (by norm_num)

theorem sum_1_218_2 : blockSum (rowCell 1) 218 2 ≤ (5339512144605530370584431 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_218) (by simpa only [blockSum_one] using cell_1_219) (by norm_num)

theorem sum_1_216_4 : blockSum (rowCell 1) 216 4 ≤ (58775053682687141155223419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_216_2 sum_1_218_2 (by norm_num)

theorem sum_1_220_2 : blockSum (rowCell 1) 220 2 ≤ (5548900674126071802411307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_220) (by simpa only [blockSum_one] using cell_1_221) (by norm_num)

theorem sum_1_222_2 : blockSum (rowCell 1) 222 2 ≤ (3686580213364413355911973 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_222) (by simpa only [blockSum_one] using cell_1_223) (by norm_num)

theorem sum_1_220_4 : blockSum (rowCell 1) 220 4 ≤ (40628503763326353989205093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_220_2 sum_1_222_2 (by norm_num)

theorem sum_1_216_8 : blockSum (rowCell 1) 216 8 ≤ (3106361170187921723263391 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_216_4 sum_1_220_4 (by norm_num)

theorem sum_1_208_16 : blockSum (rowCell 1) 208 16 ≤ (152711223419741810413654241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_208_8 sum_1_216_8 (by norm_num)

theorem sum_1_192_32 : blockSum (rowCell 1) 192 32 ≤ (390149388430490840845384757 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_192_16 sum_1_208_16 (by norm_num)

#print axioms sum_1_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
