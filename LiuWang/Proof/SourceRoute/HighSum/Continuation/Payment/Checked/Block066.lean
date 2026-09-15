import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_64_0 : expNegUpper (30689087003322160943 / 404859561279048000 : ℝ) ≤ (1202615654316064675017934693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_64_1 : expNegUpper (1963414346367139934503 / 25911011921859072000 : ℝ) ≤ (77183664800009744706613799 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_64 : rowCell 4 64 ≤ (177748648898378230175844869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1202615654316064675017934693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77183664800009744706613799 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_64_1
  · norm_num [gridPoint]

theorem exp_4_65_0 : expNegUpper (49498404744628027812167 / 653226219073131008000 : ℝ) ≤ (1234936776288658372101229927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_65_1 : expNegUpper (24741009585304109817703 / 326613109536565504000 : ℝ) ≤ (1266305806992455607401860941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361447 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_65 : rowCell 4 65 ≤ (91196428191496124005603173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1234936776288658372101229927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1266305806992455607401860941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_65_1
  · norm_num [gridPoint]

theorem exp_4_66_0 : expNegUpper (24948329265535799966807 / 329349989202770176000 : ℝ) ≤ (1266303930865093766580084723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361447 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_66_1 : expNegUpper (9976214251989698327201 / 131739995681108070400 : ℝ) ≤ (40519584753725406989704197 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806901 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_66 : rowCell 4 66 ≤ (93445602559707603679103503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1266303930865093766580084723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40519584753725406989704197 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_66_1
  · norm_num [gridPoint]

theorem exp_4_67_0 : expNegUpper (10059462111396964120441 / 132839315208740966400 : ℝ) ≤ (1296624822798594464286330073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806901 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_67_1 : expNegUpper (12570631229884490273359 / 166049144010926208000 : ℝ) ≤ (331453143236519755148247541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_67 : rowCell 4 67 ≤ (191230490993799329872484103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1296624822798594464286330073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (331453143236519755148247541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_67_1
  · norm_num [gridPoint]

theorem exp_4_68_0 : expNegUpper (12675092703676584136751 / 167429002996906112000 : ℝ) ≤ (1325810672875186648760904413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806587 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_68_1 : expNegUpper (50686390141715274736763 / 669716011987624448000 : ℝ) ≤ (1353778572632550313119540873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451573 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_68 : rowCell 4 68 ≤ (4884951380647173502943719 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1325810672875186648760904413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1353778572632550313119540873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_68_1
  · norm_num [gridPoint]

theorem exp_4_69_0 : expNegUpper (2044233971862991779883 / 27010331449491968000 : ℝ) ≤ (676888332132500601996381841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451573 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_69_1 : expNegUpper (1021853538376381585901 / 13505165724745984000 : ℝ) ≤ (1380444274083799445075028079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_69 : rowCell 4 69 ≤ (199381847351018841080606523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (676888332132500601996381841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1380444274083799445075028079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_69_1
  · norm_num [gridPoint]

theorem exp_4_70_0 : expNegUpper (25756877997464420590741 / 340411699396364544000 : ℝ) ≤ (1380442359874239328090170639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_70_1 : expNegUpper (51501395243188021497361 / 680823398792729088000 : ℝ) ≤ (351433501396035587908627391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_70 : rowCell 4 70 ≤ (203170483774553533600314059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1380442359874239328090170639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (351433501396035587908627391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_70_1
  · norm_num [gridPoint]

theorem exp_4_71_0 : expNegUpper (51924100902107123329289 / 686411349653914112000 : ℝ) ≤ (175716510997354240825064823 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_71_1 : expNegUpper (1297813877679018701819 / 17160283741347852800 : ℝ) ≤ (714788606166978958835040129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451381 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_71 : rowCell 4 71 ≤ (41350660305401656211626931 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (175716510997354240825064823 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (714788606166978958835040129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_71_1
  · norm_num [gridPoint]

theorem exp_4_72_0 : expNegUpper (1308422350261207191739 / 17300553470521356800 : ℝ) ≤ (357393823440404442892622317 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451381 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_72_1 : expNegUpper (52326166503075905750311 / 692022138820854272000 : ℝ) ≤ (725954385933337433287335191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361061 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_72 : rowCell 4 72 ≤ (105060203449477656046356063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (357393823440404442892622317 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (725954385933337433287335191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_72_1
  · norm_num [gridPoint]

theorem exp_4_73_0 : expNegUpper (52752145312290980931359 / 697655766293549568000 : ℝ) ≤ (725953427364804994534883439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361061 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_73_1 : expNegUpper (26371119711636070629539 / 348827883146774784000 : ℝ) ≤ (294533854337351796534343549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361021 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_73 : rowCell 4 73 ≤ (53315679671786300656471777 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (725953427364804994534883439 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (294533854337351796534343549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_73_1
  · norm_num [gridPoint]

theorem exp_4_74_0 : expNegUpper (340287134719832639 / 4501198285260800 : ℝ) ≤ (736333679176174903563719231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (361021 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_74_1 : expNegUpper (680458033409127697 / 9002396570521600 : ℝ) ≤ (74590262391951741435341873 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_74 : rowCell 4 74 ≤ (108086002918416446358584579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (736333679176174903563719231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (74590262391951741435341873 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_74_1
  · norm_num [gridPoint]

theorem exp_4_75_0 : expNegUpper (53590062465835541135797 / 708991536156205568000 : ℝ) ≤ (745901670315803705277405141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_75_1 : expNegUpper (13395452451465608171629 / 177247884039051392000 : ℝ) ≤ (12074155067918853093453549 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_75 : rowCell 4 75 ≤ (54710229829803184050585201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (745901670315803705277405141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12074155067918853093453549 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_75_1
  · norm_num [gridPoint]

theorem exp_4_76_0 : expNegUpper (13503187075553675384141 / 178673419636541568000 : ℝ) ≤ (377316871170745519307292197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_76_1 : expNegUpper (10801065450586756412663 / 142938735709233254400 : ℝ) ≤ (1525020666967480088326851107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451153 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_76 : rowCell 4 76 ≤ (110631509068306474787223419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (377316871170745519307292197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1525020666967480088326851107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_76_1
  · norm_num [gridPoint]

theorem exp_4_77_0 : expNegUpper (10887586460289995555023 / 144083731848376422400 : ℝ) ≤ (152501877877673467408850441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451153 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_77_1 : expNegUpper (27215673096820398093793 / 360209329620941056000 : ℝ) ≤ (769512254534292636214348709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_77 : rowCell 4 77 ≤ (223432789401072154029673807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (152501877877673467408850441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (769512254534292636214348709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_77_1
  · norm_num [gridPoint]

theorem exp_4_78_0 : expNegUpper (27432812227940008290257 / 363083239121676544000 : ℝ) ≤ (1539022633644800080425396781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451121 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_78_1 : expNegUpper (54859876620322121788393 / 726166478243353088000 : ℝ) ≤ (775626409893317304155591971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451093 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_78 : rowCell 4 78 ≤ (225345662483572909807274629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1539022633644800080425396781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (775626409893317304155591971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_78_1
  · norm_num [gridPoint]

theorem exp_4_79_0 : expNegUpper (96166669144075590751 / 1272934148783616000 : ℝ) ≤ (775625479604829288636212311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451093 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_79_1 : expNegUpper (6009883535360478869 / 79558384298976000 : ℝ) ≤ (1561684044952294002541380767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_79 : rowCell 4 79 ≤ (14187376080064523992143351 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (775625479604829288636212311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1561684044952294002541380767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_79_1
  · norm_num [gridPoint]

theorem exp_4_80_0 : expNegUpper (3483035824979935550507 / 46108164447722528000 : ℝ) ≤ (195210275153161217085026737 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_80_1 : expNegUpper (55724511900962294335871 / 737730631163560448000 : ℝ) ≤ (785151581796753747349217529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9021 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_80 : rowCell 4 80 ≤ (228387186695687898500268649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (195210275153161217085026737 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (785151581796753747349217529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_80_1
  · norm_num [gridPoint]

theorem exp_4_81_0 : expNegUpper (1811737089475005667369 / 23985385970396672000 : ℝ) ≤ (785150669318897197910238233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9021 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_81_1 : expNegUpper (181163344321285273357 / 2398538597039667200 : ℝ) ≤ (394275411780088396352764353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_81 : rowCell 4 81 ≤ (229511453466354167877480339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (785150669318897197910238233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (394275411780088396352764353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_81_1
  · norm_num [gridPoint]

theorem exp_4_82_0 : expNegUpper (5660167447232073205187 / 74938613730678835200 : ℝ) ≤ (197137480346351042791970719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804139 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_82_1 : expNegUpper (56599313033563473538261 / 749386137306788352000 : ℝ) ≤ (791038690857625367798751749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360819 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_82 : rowCell 4 82 ≤ (9214801661312442086263873 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (197137480346351042791970719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (791038690857625367798751749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_82_1
  · norm_num [gridPoint]

theorem exp_4_83_0 : expNegUpper (57042057287804284627469 / 755248147837035008000 : ℝ) ≤ (1582075599716270775331529351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360819 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_83_1 : expNegUpper (14260137693799014364427 / 188812036959258752000 : ℝ) ≤ (396308638890130370317157923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902033 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_83 : rowCell 4 83 ≤ (230963102153001322844326783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1582075599716270775331529351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (396308638890130370317157923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_83_1
  · norm_num [gridPoint]

theorem exp_4_84_0 : expNegUpper (574850082125144801443 / 7611329966730368000 : ℝ) ≤ (1585232797562552738340473027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_84_1 : expNegUpper (2299374398273393329123 / 30445319866921472000 : ℝ) ≤ (317316702552249892901486711 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360811 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_84 : rowCell 4 84 ≤ (23129169502752796317271097 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1585232797562552738340473027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (317316702552249892901486711 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_84_1
  · norm_num [gridPoint]

theorem exp_4_85_0 : expNegUpper (57930537238789965331427 / 767040683814793728000 : ℝ) ≤ (793290890158937891802264533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360811 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_85_1 : expNegUpper (28965375285409223789213 / 383520341907396864000 : ℝ) ≤ (99133786001289259500348207 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_85 : rowCell 4 85 ≤ (23135776471694572985931817 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (793290890158937891802264533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99133786001289259500348207 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_85_1
  · norm_num [gridPoint]

theorem exp_4_86_0 : expNegUpper (29189327179484693458957 / 386485604631152896000 : ℝ) ≤ (793069435293107915354720319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_86_1 : expNegUpper (2335189304379421889513 / 30918848370492231680 : ℝ) ≤ (791963920148414860523438443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_86 : rowCell 4 86 ≤ (11558205633220112031015429 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (793069435293107915354720319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (791963920148414860523438443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_86_1
  · norm_num [gridPoint]

theorem exp_4_87_0 : expNegUpper (2353174782615655665313 / 31156982920622919680 : ℝ) ≤ (395981540806179286519468501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_87_1 : expNegUpper (7353914508146847366917 / 97365571626946624000 : ℝ) ≤ (315994587962879976836292737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_87 : rowCell 4 87 ≤ (115357182579606400276608889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (395981540806179286519468501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (315994587962879976836292737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_87_1
  · norm_num [gridPoint]

theorem exp_4_88_0 : expNegUpper (7410336606299328275653 / 98112596884324416000 : ℝ) ≤ (1579971292355618934088392399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_88_1 : expNegUpper (59285510930224789400023 / 784900775074595328000 : ℝ) ≤ (196788598864904007863482653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_88 : rowCell 4 88 ≤ (230012937595914451949909429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1579971292355618934088392399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (196788598864904007863482653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_88_1
  · norm_num [gridPoint]

theorem exp_4_89_0 : expNegUpper (2389545368252709494567 / 31635992617574912000 : ℝ) ≤ (6297228696886979826006689 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (451041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_89_1 : expNegUpper (1194846543939484507219 / 15817996308787456000 : ℝ) ≤ (1566973313354535612837757563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180423 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_89 : rowCell 4 89 ≤ (114532497699125217965402619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6297228696886979826006689 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1566973313354535612837757563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_89_1
  · norm_num [gridPoint]

theorem exp_4_90_0 : expNegUpper (30098601812749685919371 / 398460847054952704000 : ℝ) ≤ (1566971728462968185915853799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (180423 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_90_1 : expNegUpper (60201774857761733547181 / 796921694109905408000 : ℝ) ≤ (389502283149107172561725347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_90 : rowCell 4 90 ≤ (56969102997110894565417259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1566971728462968185915853799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (389502283149107172561725347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_90_1
  · norm_num [gridPoint]

theorem exp_4_91_0 : expNegUpper (60658411100278176357989 / 802966411086193152000 : ℝ) ≤ (1558007580452278689602687043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_91_1 : expNegUpper (3033193195246298034389 / 40148320554309657600 : ℝ) ≤ (773731632961335020608586477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902203 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_91 : rowCell 4 91 ≤ (226453724189124801444384537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1558007580452278689602687043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (773731632961335020608586477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_91_1
  · norm_num [gridPoint]

theorem exp_4_92_0 : expNegUpper (3056113331149639882549 / 40451698318411801600 : ℝ) ≤ (1547461747364966937368417417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902203 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_92_1 : expNegUpper (61128604330805553511811 / 809033966368236032000 : ℝ) ≤ (767693397448826840083697209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_92 : rowCell 4 92 ≤ (224804085448527484503922467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1547461747364966937368417417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (767693397448826840083697209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_92_1
  · norm_num [gridPoint]

theorem exp_4_93_0 : expNegUpper (61588780185981882446779 / 815124359956034048000 : ℝ) ≤ (767692655332022359078052431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804517 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_93_1 : expNegUpper (30798003063869579374169 / 407562179978017024000 : ℝ) ≤ (760917263471200308264591971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_93 : rowCell 4 93 ≤ (222935217279209843345981641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (767692655332022359078052431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (760917263471200308264591971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_93_1
  · norm_num [gridPoint]

theorem exp_4_94_0 : expNegUpper (1241159235631681549489 / 16424751836991744000 : ℝ) ≤ (1521833077670636343983609077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (902321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_94_1 : expNegUpper (2482643171522616925057 / 32849503673983488000 : ℝ) ≤ (1506864648621353801472007913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_94 : rowCell 4 94 ≤ (220855359296825386866519899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1521833077670636343983609077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1506864648621353801472007913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_94_1
  · norm_num [gridPoint]

theorem exp_4_95_0 : expNegUpper (62529821402138029463057 / 827373662048895488000 : ℝ) ≤ (753431617425572564266856759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1804781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_95_1 : expNegUpper (1954338556378843542973 / 25855426939027984000 : ℝ) ≤ (745269186609967264560437601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (360987 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_95 : rowCell 4 95 ≤ (109286609119275189998401267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (753431617425572564266856759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (745269186609967264560437601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_95_1
  · norm_num [gridPoint]

theorem sum_4_64_2 : blockSum (rowCell 4) 64 2 ≤ (72028301056274095637410243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_64) (by simpa only [blockSum_one] using cell_4_65) (by norm_num)

theorem sum_4_66_2 : blockSum (rowCell 4) 66 2 ≤ (378121696113214537230691109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_66) (by simpa only [blockSum_one] using cell_4_67) (by norm_num)

theorem sum_4_64_4 : blockSum (rowCell 4) 64 4 ≤ (184565800348646253854435581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_64_2 sum_4_66_2 (by norm_num)

theorem sum_4_68_2 : blockSum (rowCell 4) 68 2 ≤ (394779902576905781198355283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_68) (by simpa only [blockSum_one] using cell_4_69) (by norm_num)

theorem sum_4_70_2 : blockSum (rowCell 4) 70 2 ≤ (204961892650780907329224357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_70) (by simpa only [blockSum_one] using cell_4_71) (by norm_num)

theorem sum_4_68_4 : blockSum (rowCell 4) 68 4 ≤ (804703687878467595856803997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_68_2 sum_4_70_2 (by norm_num)

theorem sum_4_64_8 : blockSum (rowCell 4) 64 8 ≤ (1542966889273052611274546321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_64_4 sum_4_68_4 (by norm_num)

theorem sum_4_72_2 : blockSum (rowCell 4) 72 2 ≤ (211691562793050257359299617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_72) (by simpa only [blockSum_one] using cell_4_73) (by norm_num)

theorem sum_4_74_2 : blockSum (rowCell 4) 74 2 ≤ (217506462578022814459754981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_74) (by simpa only [blockSum_one] using cell_4_75) (by norm_num)

theorem sum_4_72_4 : blockSum (rowCell 4) 72 4 ≤ (214599012685536535909527299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_72_2 sum_4_74_2 (by norm_num)

theorem sum_4_76_2 : blockSum (rowCell 4) 76 2 ≤ (88939161507537020720824129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_76) (by simpa only [blockSum_one] using cell_4_77) (by norm_num)

theorem sum_4_78_2 : blockSum (rowCell 4) 78 2 ≤ (90468735952921058736313649 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_78) (by simpa only [blockSum_one] using cell_4_79) (by norm_num)

theorem sum_4_76_4 : blockSum (rowCell 4) 76 4 ≤ (89703948730229039728568889 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_76_2 sum_4_78_2 (by norm_num)

theorem sum_4_72_8 : blockSum (rowCell 4) 72 8 ≤ (877717769022218270461899043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_72_4 sum_4_76_4 (by norm_num)

theorem sum_4_64_16 : blockSum (rowCell 4) 64 16 ≤ (3298402427317489152198344407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_64_8 sum_4_72_8 (by norm_num)

theorem sum_4_80_2 : blockSum (rowCell 4) 80 2 ≤ (114474660040510516594437247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_80) (by simpa only [blockSum_one] using cell_4_81) (by norm_num)

theorem sum_4_82_2 : blockSum (rowCell 4) 82 2 ≤ (57666642960726546875115451 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_82) (by simpa only [blockSum_one] using cell_4_83) (by norm_num)

theorem sum_4_80_4 : blockSum (rowCell 4) 80 4 ≤ (229807945961963610344668149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_80_2 sum_4_82_2 (by norm_num)

theorem sum_4_84_2 : blockSum (rowCell 4) 84 2 ≤ (23132472987223684651601457 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_84) (by simpa only [blockSum_one] using cell_4_85) (by norm_num)

theorem sum_4_86_2 : blockSum (rowCell 4) 86 2 ≤ (230939238911807520586763179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_86) (by simpa only [blockSum_one] using cell_4_87) (by norm_num)

theorem sum_4_84_4 : blockSum (rowCell 4) 84 4 ≤ (462263968784044367102777749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_84_2 sum_4_86_2 (by norm_num)

theorem sum_4_80_8 : blockSum (rowCell 4) 80 8 ≤ (921879860707971587792114047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_80_4 sum_4_84_4 (by norm_num)

theorem sum_4_88_2 : blockSum (rowCell 4) 88 2 ≤ (459077932994164887880714667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_88) (by simpa only [blockSum_one] using cell_4_89) (by norm_num)

theorem sum_4_90_2 : blockSum (rowCell 4) 90 2 ≤ (454330136177568379706053573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_90) (by simpa only [blockSum_one] using cell_4_91) (by norm_num)

theorem sum_4_88_4 : blockSum (rowCell 4) 88 4 ≤ (11417600864646665844834603 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_88_2 sum_4_90_2 (by norm_num)

theorem sum_4_92_2 : blockSum (rowCell 4) 92 2 ≤ (111934825681934331962476027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_92) (by simpa only [blockSum_one] using cell_4_93) (by norm_num)

theorem sum_4_94_2 : blockSum (rowCell 4) 94 2 ≤ (439428577535375766863322433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_94) (by simpa only [blockSum_one] using cell_4_95) (by norm_num)

theorem sum_4_92_4 : blockSum (rowCell 4) 92 4 ≤ (887167880263113094713226541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_92_2 sum_4_94_2 (by norm_num)

theorem sum_4_88_8 : blockSum (rowCell 4) 88 8 ≤ (1800575949434846362299994781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_88_4 sum_4_92_4 (by norm_num)

theorem sum_4_80_16 : blockSum (rowCell 4) 80 16 ≤ (29154685366806316303073783 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_80_8 sum_4_88_8 (by norm_num)

theorem sum_4_64_32 : blockSum (rowCell 4) 64 32 ≤ (3471369049084139345041283641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_64_16 sum_4_80_16 (by norm_num)

#print axioms sum_4_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
