import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_160_0 : expNegUpper (1001816620787031768137 / 13283399904673968000 : ℝ) ≤ (220507391046917208229371747 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_160_1 : expNegUpper (32086143235500371946917 / 425068796949566976000 : ℝ) ≤ (1651557921363980174348482247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_160 : rowCell 2 160 ≤ (62267465996358545518637417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (220507391046917208229371747 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1651557921363980174348482247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_160_1
  · norm_num [gridPoint]

theorem exp_2_161_0 : expNegUpper (96835388944579375112039 / 1282849789227848192000 : ℝ) ≤ (82577866686682679153607203 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_161_1 : expNegUpper (1938410755649585750223 / 25656995784556963840 : ℝ) ≤ (1545494507009631130621933929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225553 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_161 : rowCell 2 161 ≤ (233131892578263489117432127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82577866686682679153607203 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1545494507009631130621933929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_161_1
  · norm_num [gridPoint]

theorem exp_2_162_0 : expNegUpper (1949994596104895765823 / 25810320518255011840 : ℝ) ≤ (61819758545621283457794617 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225553 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_162_1 : expNegUpper (97585996700878095899461 / 1290516025912750592000 : ℝ) ≤ (14455599488870791159698907 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_162 : rowCell 2 162 ≤ (218110338576512945405773687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61819758545621283457794617 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14455599488870791159698907 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_162_1
  · norm_num [gridPoint]

theorem exp_2_163_0 : expNegUpper (32722476056629978669183 / 432735033634469376000 : ℝ) ≤ (722779723332342016292834057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1805367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_163_1 : expNegUpper (8187901371169682311229 / 108183758408617344000 : ℝ) ≤ (337863722714726515932075417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_163 : rowCell 2 163 ≤ (101980399217394529336845917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (722779723332342016292834057 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (337863722714726515932075417 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_163_1
  · norm_num [gridPoint]

theorem exp_2_164_0 : expNegUpper (988384940308534649903 / 13059170141998208000 : ℝ) ≤ (675727213434066119088053451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_164_1 : expNegUpper (3957080281371688389843 / 52236680567992832000 : ℝ) ≤ (1262890241901790772096609211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807273 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_164 : rowCell 2 164 ≤ (190640362071991133886791001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (675727213434066119088053451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1262890241901790772096609211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_164_1
  · norm_num [gridPoint]

theorem exp_2_165_0 : expNegUpper (99512937380474021968467 / 1313651765801988608000 : ℝ) ≤ (157861226676996086324890731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807273 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_165_1 : expNegUpper (49801289216992404331253 / 656825882900994304000 : ℝ) ≤ (589793592133955811864975899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_165 : rowCell 2 165 ≤ (178107617084036159132096247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (157861226676996086324890731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (589793592133955811864975899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_165_1
  · norm_num [gridPoint]

theorem exp_2_166_0 : expNegUpper (2385494481216434611217 / 31462127516902656000 : ℝ) ≤ (589793394369106679574529761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_166_1 : expNegUpper (955062291861453630601 / 12584851006761062400 : ℝ) ≤ (1101277143832854116714429341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226151 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_166 : rowCell 2 166 ≤ (83161323588385829829200477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (589793394369106679574529761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1101277143832854116714429341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_166_1
  · norm_num [gridPoint]

theorem exp_2_167_0 : expNegUpper (20174399303008161365461 / 265837956784717926400 : ℝ) ≤ (220255355775634606920076781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226151 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_167_1 : expNegUpper (12620487957629290515867 / 166148722990448704000 : ℝ) ≤ (1027701726119391460025886269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362037 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_167 : rowCell 2 167 ≤ (77623512669273993348749131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (220255355775634606920076781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1027701726119391460025886269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_167_1
  · norm_num [gridPoint]

theorem exp_2_168_0 : expNegUpper (12694579035583041020763 / 167124131305377856000 : ℝ) ≤ (1027701389516666937759454627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (362037 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_168_1 : expNegUpper (101649677473068534133063 / 1336993050443022848000 : ℝ) ≤ (958612621335329631619401501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181117 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_168 : rowCell 2 168 ≤ (144843802250321714679773991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1027701389516666937759454627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (958612621335329631619401501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_168_1
  · norm_num [gridPoint]

theorem exp_2_169_0 : expNegUpper (1363262473497326192221 / 17930922070242816000 : ℝ) ≤ (479306155505154586007704447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181117 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_169_1 : expNegUpper (682259147159292719737 / 8965461035121408000 : ℝ) ≤ (893771481607885230743169629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_169 : rowCell 2 169 ≤ (5403099616351296650327571 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (479306155505154586007704447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (893771481607885230743169629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_169_1
  · norm_num [gridPoint]

theorem exp_2_170_0 : expNegUpper (51468083095142431153891 / 676334049199577344000 : ℝ) ≤ (893771195626315205042633361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812161 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_170_1 : expNegUpper (103031497455849092338461 / 1352668098399154688000 : ℝ) ≤ (208237443359564871156938569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_170 : rowCell 2 170 ≤ (62957022207529715162293709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (893771195626315205042633361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (208237443359564871156938569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_170_1
  · norm_num [gridPoint]

theorem exp_2_171_0 : expNegUpper (103631084310959168568789 / 1360539879835853312000 : ℝ) ≤ (832949509997494757649891191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_171_1 : expNegUpper (5186378180563636699793 / 68026993991792665600 : ℝ) ≤ (775928608239517770043037553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453541 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_171 : rowCell 2 171 ≤ (58660418929138653542655607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (832949509997494757649891191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (775928608239517770043037553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_171_1
  · norm_num [gridPoint]

theorem exp_2_172_0 : expNegUpper (1738824164444350498811 / 22807241659638451200 : ℝ) ≤ (193982091415134907576566149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453541 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_172_1 : expNegUpper (34809026844167826553937 / 456144833192769024000 : ℝ) ≤ (722498553659786238056722877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72607 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_172 : rowCell 2 172 ≤ (27316659299943372294075351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (193982091415134907576566149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (722498553659786238056722877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_172_1
  · norm_num [gridPoint]

theorem exp_2_173_0 : expNegUpper (15004467549961299016637 / 196621708232359424000 : ℝ) ≤ (90312291297452170772746247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72607 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_173_1 : expNegUpper (7509289872277141147527 / 98310854116179712000 : ℝ) ≤ (672459428232217693785753537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_173 : rowCell 2 173 ≤ (101721573040336265393408089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90312291297452170772746247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (672459428232217693785753537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_173_1
  · norm_num [gridPoint]

theorem exp_2_174_0 : expNegUpper (2728685503290374319 / 35723671070464000 : ℝ) ≤ (26898368911868893685820353 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_174_1 : expNegUpper (5462529375057593287 / 71447342140928000 : ℝ) ≤ (125124016346824352256023143 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908609 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_174 : rowCell 2 174 ≤ (94657109129514316452045713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26898368911868893685820353 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (125124016346824352256023143 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_174_1
  · norm_num [gridPoint]

theorem exp_2_175_0 : expNegUpper (35481777022439470630699 / 464085129546733056000 : ℝ) ≤ (62561989279117887577326463 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908609 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_175_1 : expNegUpper (2219717412800516833367 / 29005320596670816000 : ℝ) ≤ (581798163480950861517706469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7273 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_175 : rowCell 2 175 ≤ (4402300472651181621740923 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62561989279117887577326463 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (581798163480950861517706469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_175_1
  · norm_num [gridPoint]

theorem exp_2_176_0 : expNegUpper (6697349142907310058629 / 87515085100354592000 : ℝ) ≤ (116359597954797508424354307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7273 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_176_1 : expNegUpper (21451971144454087398483 / 280048272321134694400 : ℝ) ≤ (135204970156807016818510631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_176 : rowCell 2 176 ≤ (20465575927912395207322957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (116359597954797508424354307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (135204970156807016818510631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_176_1
  · norm_num [gridPoint]

theorem exp_2_177_0 : expNegUpper (21574667780487259745643 / 281650034575380582400 : ℝ) ≤ (540819720989100527728689743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_177_1 : expNegUpper (53988388178808201818543 / 704125086438451456000 : ℝ) ≤ (502519748396639035420952019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455083 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_177 : rowCell 2 177 ≤ (15216250296582531039052129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (540819720989100527728689743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (502519748396639035420952019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_177_1
  · norm_num [gridPoint]

theorem exp_2_178_0 : expNegUpper (18098766484569178665269 / 236046970408981248000 : ℝ) ≤ (100503920348769614921276249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455083 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_178_1 : expNegUpper (36232402570933784888231 / 472093940817962496000 : ℝ) ≤ (116685083504484213067828903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910691 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_178 : rowCell 2 178 ≤ (70679305335222892846566897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (100503920348769614921276249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (116685083504484213067828903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_178_1
  · norm_num [gridPoint]

theorem exp_2_179_0 : expNegUpper (4372615051751677098293 / 56973452413465088000 : ℝ) ≤ (466740199345164781648115087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910691 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_179_1 : expNegUpper (1094211597801639368043 / 14243363103366272000 : ℝ) ≤ (27083249750155391627347559 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_179 : rowCell 2 179 ≤ (16408518285840930513119413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (466740199345164781648115087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27083249750155391627347559 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_179_1
  · norm_num [gridPoint]

theorem exp_2_180_0 : expNegUpper (3930060037639482566229 / 51157629875897216000 : ℝ) ≤ (27083242023590140031780613 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1822439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_180_1 : expNegUpper (15735520364577542397853 / 204630519503588864000 : ℝ) ≤ (402152620263580826400501929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_180 : rowCell 2 180 ≤ (30462139916991129604082677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27083242023590140031780613 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (402152620263580826400501929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_180_1
  · norm_num [gridPoint]

theorem exp_2_181_0 : expNegUpper (36923841060031490637313 / 480171267006457344000 : ℝ) ≤ (201076253411070796123941297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_181_1 : expNegUpper (3695988867359219377859 / 48017126700645734400 : ℝ) ≤ (46633419305925682206275497 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_181 : rowCell 2 181 ≤ (14132432192592370059311529 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201076253411070796123941297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46633419305925682206275497 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_181_1
  · norm_num [gridPoint]

theorem exp_2_182_0 : expNegUpper (11150491266469745435897 / 144863680381937715200 : ℝ) ≤ (373067250389038653409209103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_182_1 : expNegUpper (111614240178703937185761 / 1448636803819377152000 : ℝ) ≤ (172974170860460409330875799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_182 : rowCell 2 182 ≤ (13107815741807320248781911 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (373067250389038653409209103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172974170860460409330875799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_182_1
  · norm_num [gridPoint]

theorem exp_2_183_0 : expNegUpper (112241859500053105924569 / 1456782644925137408000 : ℝ) ≤ (21621765394023633501325733 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_183_1 : expNegUpper (14044046877270438883001 / 182097830615642176000 : ℝ) ≤ (160337227571591819122594539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_183 : rowCell 2 183 ≤ (9722145261677907274657503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21621765394023633501325733 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (160337227571591819122594539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_183_1
  · norm_num [gridPoint]

theorem exp_2_184_0 : expNegUpper (188303956130833455563 / 2441585540561088000 : ℝ) ≤ (160337183841225681960581887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_184_1 : expNegUpper (1507921073753252662661 / 19532684324488704000 : ℝ) ≤ (297131033633800422778037757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91391 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_184 : rowCell 2 184 ≤ (45050924923521325356070389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (160337183841225681960581887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (297131033633800422778037757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_184_1
  · norm_num [gridPoint]

theorem exp_2_185_0 : expNegUpper (113726465192377003327727 / 1473142842053923328000 : ℝ) ≤ (148565476747147566425771283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91391 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_185_1 : expNegUpper (56919683355516949910763 / 736571421026961664000 : ℝ) ≤ (137604810222699849603700783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_185 : rowCell 2 185 ≤ (8347117772783389219662777 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148565476747147566425771283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137604810222699849603700783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_185_1
  · norm_num [gridPoint]

theorem exp_2_186_0 : expNegUpper (57237072017011271311707 / 740678599038474496000 : ℝ) ≤ (137604773520198579591970617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914457 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_186_1 : expNegUpper (4583529741964880326357 / 59254287923077959680 : ℝ) ≤ (50961540989242539821426649 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366003 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_186 : rowCell 2 186 ≤ (3864933420223842258637971 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137604773520198579591970617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50961540989242539821426649 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_186_1
  · norm_num [gridPoint]

theorem exp_2_187_0 : expNegUpper (219476990849095881817 / 2837322652201390080 : ℝ) ≤ (127403818866749165454993611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366003 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_187_1 : expNegUpper (1373103821882106207629 / 17733266576258688000 : ℝ) ≤ (235828468424044924941650751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_187 : rowCell 2 187 ≤ (35777625666884680134470371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (127403818866749165454993611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (235828468424044924941650751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_187_1
  · norm_num [gridPoint]

theorem exp_2_188_0 : expNegUpper (28995075917493509012081 / 374463606260066432000 : ℝ) ≤ (117914203451387265791637621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_188_1 : expNegUpper (116096809170297286396323 / 1497854425040265728000 : ℝ) ≤ (218180534534035481193671007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366447 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_188 : rowCell 2 188 ≤ (1324269596329220330627631 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (117914203451387265791637621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (218180534534035481193671007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_188_1
  · norm_num [gridPoint]

theorem exp_2_189_0 : expNegUpper (4669552177958291345427 / 60245491839222272000 : ℝ) ≤ (218180478241795266773244659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366447 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_189_1 : expNegUpper (2337130358761234995089 / 30122745919611136000 : ℝ) ≤ (12611107808096214589906081 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366671 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_189 : rowCell 2 189 ≤ (6124745896290377617091989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (218180478241795266773244659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12611107808096214589906081 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_189_1
  · norm_num [gridPoint]

theorem exp_2_190_0 : expNegUpper (19583488754177287907507 / 252407167537767168000 : ℝ) ≤ (10088883671979735828246573 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366671 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_190_1 : expNegUpper (39206619111242986081427 / 504814335075534336000 : ℝ) ≤ (93269410269052535266921781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22931 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_190 : rowCell 2 190 ≤ (28316387618953926564895147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10088883671979735828246573 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93269410269052535266921781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_190_1
  · norm_num [gridPoint]

theorem exp_2_191_0 : expNegUpper (118266697890632014205489 / 1522771552778404352000 : ℝ) ≤ (233173466821034324764967 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22931 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_191_1 : expNegUpper (369958866717617370609 / 4758661102432513600 : ℝ) ≤ (172387328872703395325675487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_191 : rowCell 2 191 ≤ (5234642770907890328903007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (233173466821034324764967 / 1250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172387328872703395325675487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_191_1
  · norm_num [gridPoint]

theorem sum_2_160_2 : blockSum (rowCell 2) 160 2 ≤ (96440351312739534238396359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_160) (by simpa only [blockSum_one] using cell_2_161) (by norm_num)

theorem sum_2_162_2 : blockSum (rowCell 2) 162 2 ≤ (422071137011302004079465521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_162) (by simpa only [blockSum_one] using cell_2_163) (by norm_num)

theorem sum_2_160_4 : blockSum (rowCell 2) 160 4 ≤ (226068223393749918817861829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_160_2 sum_2_162_2 (by norm_num)

theorem sum_2_164_2 : blockSum (rowCell 2) 164 2 ≤ (23046748697251705813680453 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_164) (by simpa only [blockSum_one] using cell_2_165) (by norm_num)

theorem sum_2_166_2 : blockSum (rowCell 2) 166 2 ≤ (20098104532207477897243701 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_166) (by simpa only [blockSum_one] using cell_2_167) (by norm_num)

theorem sum_2_164_4 : blockSum (rowCell 2) 164 4 ≤ (21572426614729591855462077 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_164_2 sum_2_166_2 (by norm_num)

theorem sum_2_160_8 : blockSum (rowCell 2) 160 8 ≤ (79729527262317330732311689 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_160_4 sum_2_164_4 (by norm_num)

theorem sum_2_168_2 : blockSum (rowCell 2) 168 2 ≤ (139960646329552065468981633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_168) (by simpa only [blockSum_one] using cell_2_169) (by norm_num)

theorem sum_2_170_2 : blockSum (rowCell 2) 170 2 ≤ (30404360284167092176237329 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_170) (by simpa only [blockSum_one] using cell_2_171) (by norm_num)

theorem sum_2_168_4 : blockSum (rowCell 2) 168 4 ≤ (261578087466220434173930949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_168_2 sum_2_170_2 (by norm_num)

theorem sum_2_172_2 : blockSum (rowCell 2) 172 2 ≤ (210988210240109754569709493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_172) (by simpa only [blockSum_one] using cell_2_173) (by norm_num)

theorem sum_2_174_2 : blockSum (rowCell 2) 174 2 ≤ (182703118582537948886864173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_174) (by simpa only [blockSum_one] using cell_2_175) (by norm_num)

theorem sum_2_172_4 : blockSum (rowCell 2) 172 4 ≤ (196845664411323851728286833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_172_2 sum_2_174_2 (by norm_num)

theorem sum_2_168_8 : blockSum (rowCell 2) 168 8 ≤ (229211875938772142951108891 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_168_4 sum_2_172_4 (by norm_num)

theorem sum_2_160_16 : blockSum (rowCell 2) 160 16 ≤ (78482439031294849576583417 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_160_8 sum_2_168_8 (by norm_num)

theorem sum_2_176_2 : blockSum (rowCell 2) 176 2 ≤ (157943555194562236024552473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_176) (by simpa only [blockSum_one] using cell_2_177) (by norm_num)

theorem sum_2_178_2 : blockSum (rowCell 2) 178 2 ≤ (136313378478586614899044549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_178) (by simpa only [blockSum_one] using cell_2_179) (by norm_num)

theorem sum_2_176_4 : blockSum (rowCell 2) 176 4 ≤ (147128466836574425461798511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_176_2 sum_2_178_2 (by norm_num)

theorem sum_2_180_2 : blockSum (rowCell 2) 180 2 ≤ (11745400860435173944541147 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_180) (by simpa only [blockSum_one] using cell_2_181) (by norm_num)

theorem sum_2_182_2 : blockSum (rowCell 2) 182 2 ≤ (101041989275618817368415159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_182) (by simpa only [blockSum_one] using cell_2_183) (by norm_num)

theorem sum_2_180_4 : blockSum (rowCell 2) 180 4 ≤ (218495997879970556813826629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_180_2 sum_2_182_2 (by norm_num)

theorem sum_2_176_8 : blockSum (rowCell 2) 176 8 ≤ (512752931553119407737423651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_176_4 sum_2_180_4 (by norm_num)

theorem sum_2_184_2 : blockSum (rowCell 2) 184 2 ≤ (43393256893719135727192137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_184) (by simpa only [blockSum_one] using cell_2_185) (by norm_num)

theorem sum_2_186_2 : blockSum (rowCell 2) 186 2 ≤ (74426959869123102720850081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_186) (by simpa only [blockSum_one] using cell_2_187) (by norm_num)

theorem sum_2_184_4 : blockSum (rowCell 2) 184 4 ≤ (32242694731312274835046871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_184_2 sum_2_186_2 (by norm_num)

theorem sum_2_188_2 : blockSum (rowCell 2) 188 2 ≤ (99578858421378744298673 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_188) (by simpa only [blockSum_one] using cell_2_189) (by norm_num)

theorem sum_2_190_2 : blockSum (rowCell 2) 190 2 ≤ (27244800736746689104705091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_190) (by simpa only [blockSum_one] using cell_2_191) (by norm_num)

theorem sum_2_188_4 : blockSum (rowCell 2) 188 4 ≤ (59110035431587887280280451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_188_2 sum_2_190_2 (by norm_num)

theorem sum_2_184_8 : blockSum (rowCell 2) 184 8 ≤ (279433544519737148735795257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_184_4 sum_2_188_4 (by norm_num)

theorem sum_2_176_16 : blockSum (rowCell 2) 176 16 ≤ (198046619018214139118304727 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_176_8 sum_2_184_8 (by norm_num)

theorem sum_2_160_32 : blockSum (rowCell 2) 160 32 ≤ (825906131268572935730972063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_160_16 sum_2_176_16 (by norm_num)

#print axioms sum_2_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
