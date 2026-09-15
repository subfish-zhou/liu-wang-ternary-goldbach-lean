import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_160_0 : expNegUpper (342400716426354589379 / 4427799968224656000 : ℝ) ≤ (260942777954753130657774969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73187 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_160_1 : expNegUpper (10965350967490673315639 / 141689598983188992000 : ℝ) ≤ (239941805208005713300023 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228817 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_160 : rowCell 3 160 ≤ (18472438172962330814453397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (260942777954753130657774969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239941805208005713300023 / 976562500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_160_1
  · norm_num [gridPoint]

theorem exp_3_161_0 : expNegUpper (99279681414134575112039 / 1282849789227848192000 : ℝ) ≤ (122850157433767017256073263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228817 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_161_1 : expNegUpper (1987150970354287190223 / 25656995784556963840 : ℝ) ≤ (231230263437954838739896559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457851 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_161 : rowCell 3 161 ≤ (6955641252470538995039709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (122850157433767017256073263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (231230263437954838739896559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_161_1
  · norm_num [gridPoint]

theorem exp_3_162_0 : expNegUpper (1999026080182402325823 / 25810320518255011840 : ℝ) ≤ (231230176334503644321405553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457851 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_162_1 : expNegUpper (100030289170433295899461 / 1290516025912750592000 : ℝ) ≤ (27187784762550808411553061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45807 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_162 : rowCell 3 162 ≤ (3272197373545817670343389 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (231230176334503644321405553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27187784762550808411553061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_162_1
  · norm_num [gridPoint]

theorem exp_3_163_0 : expNegUpper (11180698234231710223061 / 144245011211489792000 : ℝ) ≤ (217502197137331195422052029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45807 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_163_1 : expNegUpper (2797399740497542103743 / 36061252802872448000 : ℝ) ≤ (51121695253960912833777867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_163 : rowCell 3 163 ≤ (15385907708826034659279373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (217502197137331195422052029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51121695253960912833777867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_163_1
  · norm_num [gridPoint]

theorem exp_3_164_0 : expNegUpper (1013046317033690489903 / 13059170141998208000 : ℝ) ≤ (204486705795338243997617189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458291 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_164_1 : expNegUpper (4055434518899506629843 / 52236680567992832000 : ℝ) ≤ (19215464509517311373455817 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366811 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_164 : rowCell 3 164 ≤ (2892344366439977889962819 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (204486705795338243997617189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19215464509517311373455817 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_164_1
  · norm_num [gridPoint]

theorem exp_3_165_0 : expNegUpper (101986356787309733968467 / 1313651765801988608000 : ℝ) ≤ (192154575242190525929466687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366811 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_165_1 : expNegUpper (51034358053250196331253 / 656825882900994304000 : ℝ) ≤ (180477332305329217939068409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1834953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_165 : rowCell 3 165 ≤ (13586326742422288473831731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (192154575242190525929466687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (180477332305329217939068409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_165_1
  · norm_num [gridPoint]

theorem exp_3_166_0 : expNegUpper (5703970519569227426173 / 73411630872772864000 : ℝ) ≤ (36095453493306888678968231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1834953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_166_1 : expNegUpper (2283443556717518738069 / 29364652349109145600 : ℝ) ≤ (4235673314516231584178439 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_166 : rowCell 3 166 ≤ (3189416079311920723586879 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36095453493306888678968231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4235673314516231584178439 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_166_1
  · norm_num [gridPoint]

theorem exp_3_167_0 : expNegUpper (20671995878103354965461 / 265837956784717926400 : ℝ) ≤ (84713436211699347231572307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_167_1 : expNegUpper (12930575600273770515867 / 166148722990448704000 : ℝ) ≤ (31795239462891725775902803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_167 : rowCell 3 167 ≤ (2993430861864690453041951 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (84713436211699347231572307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31795239462891725775902803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_167_1
  · norm_num [gridPoint]

theorem exp_3_168_0 : expNegUpper (13006487111807553020763 / 167124131305377856000 : ℝ) ≤ (19872017690725894217503763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_168_1 : expNegUpper (104137660348544502133063 / 1336993050443022848000 : ℝ) ≤ (149098567740878037277705667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_168 : rowCell 3 168 ≤ (11232542292799145458244799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19872017690725894217503763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (149098567740878037277705667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_168_1
  · norm_num [gridPoint]

theorem exp_3_169_0 : expNegUpper (465543252695180837407 / 5976974023414272000 : ℝ) ≤ (29819703205323003905714523 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_169_1 : expNegUpper (232964748185977786579 / 2988487011707136000 : ℝ) ≤ (69884099257782471793860897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_169 : rowCell 3 169 ≤ (21064420353104609400250801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29819703205323003905714523 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69884099257782471793860897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_169_1
  · norm_num [gridPoint]

theorem exp_3_170_0 : expNegUpper (52722997134360607153891 / 676334049199577344000 : ℝ) ≤ (34942037649819998099470913 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_170_1 : expNegUpper (105534043799965316338461 / 1352668098399154688000 : ℝ) ≤ (32739994200280624823514971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459889 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_170 : rowCell 3 170 ≤ (19741738282339310993290153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34942037649819998099470913 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32739994200280624823514971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_170_1
  · norm_num [gridPoint]

theorem exp_3_171_0 : expNegUpper (106148194123715648568789 / 1360539879835853312000 : ℝ) ≤ (32739983105825429611807447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459889 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_171_1 : expNegUpper (5311869584485454299793 / 68026993991792665600 : ℝ) ≤ (61324768579217008145915947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_171 : rowCell 3 171 ≤ (9246715187078998558935779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32739983105825429611807447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61324768579217008145915947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_171_1
  · norm_num [gridPoint]

theorem exp_3_172_0 : expNegUpper (593632452298542432937 / 7602413886546150400 : ℝ) ≤ (122649496075587220473699371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_172_1 : expNegUpper (11882687816139995517979 / 152048277730923008000 : ℝ) ≤ (114813272539382309416656033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_172 : rowCell 3 172 ≤ (17315998432859755631291727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (122649496075587220473699371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (114813272539382309416656033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_172_1
  · norm_num [gridPoint]

theorem exp_3_173_0 : expNegUpper (107562946131125829116459 / 1376351957626515968000 : ℝ) ≤ (22962646904640302587380999 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_173_1 : expNegUpper (53827224879478292032689 / 688175978813257984000 : ℝ) ≤ (107428341669457734955344501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (368481 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_173 : rowCell 3 173 ≤ (8103027703067411474297931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22962646904640302587380999 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107428341669457734955344501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_173_1
  · norm_num [gridPoint]

theorem exp_3_174_0 : expNegUpper (2794206923050809519 / 35723671070464000 : ℝ) ≤ (107428306506007051989735777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (368481 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_174_1 : expNegUpper (5593196383129682887 / 71447342140928000 : ℝ) ≤ (100472673100803719410298279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_174 : rowCell 3 174 ≤ (7580163109482503472271457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (107428306506007051989735777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100472673100803719410298279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_174_1
  · norm_num [gridPoint]

theorem exp_3_175_0 : expNegUpper (12110174201928378210233 / 154695043182244352000 : ℝ) ≤ (100472640589740664756232601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_175_1 : expNegUpper (757537436320428277789 / 9668440198890272000 : ℝ) ≤ (9392496620744283951866023 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92217 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_175 : rowCell 3 175 ≤ (55373625553712804594843 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (100472640589740664756232601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9392496620744283951866023 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_175_1
  · norm_num [gridPoint]

theorem exp_3_176_0 : expNegUpper (6856944048179630058629 / 87515085100354592000 : ℝ) ≤ (23481234040317720999655149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92217 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_176_1 : expNegUpper (21961218494461485798483 / 280048272321134694400 : ℝ) ≤ (17552937876981955156092613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_176 : rowCell 3 176 ≤ (13248970731600445357777301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23481234040317720999655149 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17552937876981955156092613 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_176_1
  · norm_num [gridPoint]

theorem exp_3_177_0 : expNegUpper (22086827824222709345643 / 281650034575380582400 : ℝ) ≤ (87764661628261889980826967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_177_1 : expNegUpper (55265147420986761818543 / 704125086438451456000 : ℝ) ≤ (10246509463302529483877817 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_177 : rowCell 3 177 ≤ (12377355384294969745589311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (87764661628261889980826967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10246509463302529483877817 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_177_1
  · norm_num [gridPoint]

theorem exp_3_178_0 : expNegUpper (6175593381134024888423 / 78682323469660416000 : ℝ) ≤ (81972050075373049044080597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_178_1 : expNegUpper (12362000881275400296077 / 157364646939320832000 : ℝ) ≤ (38264058138574258728786021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923647 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_178 : rowCell 3 178 ≤ (2311594906583815994579083 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81972050075373049044080597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38264058138574258728786021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_178_1
  · norm_num [gridPoint]

theorem exp_3_179_0 : expNegUpper (4475629599244377258293 / 56973452413465088000 : ℝ) ≤ (19132023154641656079900237 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923647 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_179_1 : expNegUpper (1119892417331613128043 / 14243363103366272000 : ℝ) ≤ (71414551517282843634782493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462073 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_179 : rowCell 3 179 ≤ (5394055263802742002745003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19132023154641656079900237 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71414551517282843634782493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_179_1
  · norm_num [gridPoint]

theorem exp_3_180_0 : expNegUpper (28156081618885785963603 / 358103409131280512000 : ℝ) ≤ (7141452968819270964801397 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462073 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_180_1 : expNegUpper (112724006239360300784971 / 1432413636525122048000 : ℝ) ≤ (33306930296689983249976547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_180 : rowCell 3 180 ≤ (2013030845842834629032197 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7141452968819270964801397 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33306930296689983249976547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_180_1
  · norm_num [gridPoint]

theorem exp_3_181_0 : expNegUpper (12595716704005803545771 / 160057089002152448000 : ℝ) ≤ (66613840460372811229399729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1849297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_181_1 : expNegUpper (1260692349360157925953 / 16005708900215244800 : ℝ) ≤ (15527312301560723822159083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_181 : rowCell 3 181 ≤ (1877320669628097933868803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66613840460372811229399729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15527312301560723822159083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_181_1
  · norm_num [gridPoint]

theorem exp_3_182_0 : expNegUpper (11410212155497534235897 / 144863680381937715200 : ℝ) ≤ (31054615322452936395595473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1850309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_182_1 : expNegUpper (114204167334661697185761 / 1448636803819377152000 : ℝ) ≤ (28942317966091693788999039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_182 : rowCell 3 182 ≤ (8750060557790851719753627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31054615322452936395595473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28942317966091693788999039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_182_1
  · norm_num [gridPoint]

theorem exp_3_183_0 : expNegUpper (114846350124651121924569 / 1456782644925137408000 : ℝ) ≤ (57884618826558331746908229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851327 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_183_1 : expNegUpper (14368697988555174883001 / 182097830615642176000 : ℝ) ≤ (53924637303181068127986591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_183 : rowCell 3 183 ≤ (4076615705304575550809703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57884618826558331746908229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53924637303181068127986591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_183_1
  · norm_num [gridPoint]

theorem exp_3_184_0 : expNegUpper (64218970020787898521 / 813861846853696000 : ℝ) ≤ (3370288846578126796269901 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_184_1 : expNegUpper (514215871804853180887 / 6510894774829568000 : ℝ) ≤ (10042910360036529913379969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370677 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_184 : rowCell 3 184 ≤ (7593922082887503439334273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3370288846578126796269901 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10042910360036529913379969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_184_1
  · norm_num [gridPoint]

theorem exp_3_185_0 : expNegUpper (116345519285615275327727 / 1473142842053923328000 : ℝ) ≤ (10042907457875882150147603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370677 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_185_1 : expNegUpper (58225569534976021910763 / 736571421026961664000 : ℝ) ≤ (46740342922658927057863757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_185 : rowCell 3 185 ≤ (7070036972962026096197367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10042907457875882150147603 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46740342922658927057863757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_185_1
  · norm_num [gridPoint]

theorem exp_3_186_0 : expNegUpper (58550239930790471311707 / 740678599038474496000 : ℝ) ≤ (46740329565405673323723153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_186_1 : expNegUpper (4688291905694411206357 / 59254287923077959680 : ℝ) ≤ (21744310743303924202635353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463867 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_186 : rowCell 3 186 ≤ (6579576175786036797876661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46740329565405673323723153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21744310743303924202635353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_186_1
  · norm_num [gridPoint]

theorem exp_3_187_0 : expNegUpper (523817945589572737573 / 6620419521803243520 : ℝ) ≤ (21744304597938061808110249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463867 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_187_1 : expNegUpper (3276862690712647817801 / 41377622011270272000 : ℝ) ≤ (40446627292505895256122207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_187 : rowCell 3 187 ≤ (6120632855296849346891311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21744304597938061808110249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40446627292505895256122207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_187_1
  · norm_num [gridPoint]

theorem exp_3_188_0 : expNegUpper (29655300741543173012081 / 374463606260066432000 : ℝ) ≤ (20223307993700493158998791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_188_1 : expNegUpper (118730426732175814396323 / 1497854425040265728000 : ℝ) ≤ (470027628678844488598923 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1857577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_188 : rowCell 3 188 ≤ (227655621378181984140813 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20223307993700493158998791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (470027628678844488598923 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_188_1
  · norm_num [gridPoint]

theorem exp_3_189_0 : expNegUpper (4775479419179042705427 / 60245491839222272000 : ℝ) ≤ (37602199899675428130882631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1857577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_189_1 : expNegUpper (2389948344685208115089 / 30122745919611136000 : ℝ) ≤ (34943811390508015119803959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_189 : rowCell 3 189 ≤ (2645060160668597603013681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37602199899675428130882631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34943811390508015119803959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_189_1
  · norm_num [gridPoint]

theorem exp_3_190_0 : expNegUpper (6675355293883479969169 / 84135722512589056000 : ℝ) ≤ (34943801836563900953677703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_190_1 : expNegUpper (13363115373805304693809 / 168271445025178112000 : ℝ) ≤ (32460442948545610863533563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_190 : rowCell 3 190 ≤ (4915178088231359723538069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34943801836563900953677703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32460442948545610863533563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_190_1
  · norm_num [gridPoint]

theorem exp_3_191_0 : expNegUpper (120929442389791054205489 / 1522771552778404352000 : ℝ) ≤ (1298417366820936879678457 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_191_1 : expNegUpper (378257187857738970609 / 4758661102432513600 : ℝ) ≤ (30141669164451597582371909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186079 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_191 : rowCell 3 191 ≤ (285312601203974590248721 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1298417366820936879678457 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30141669164451597582371909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_191_1
  · norm_num [gridPoint]

theorem sum_3_160_2 : blockSum (rowCell 3) 160 2 ≤ (71723082608277356604105339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_160) (by simpa only [blockSum_one] using cell_3_161) (by norm_num)

theorem sum_3_162_2 : blockSum (rowCell 3) 162 2 ≤ (15873447288277561505498159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_162) (by simpa only [blockSum_one] using cell_3_163) (by norm_num)

theorem sum_3_160_4 : blockSum (rowCell 3) 160 4 ≤ (5408674870455504105043919 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_160_2 sum_3_162_2 (by norm_num)

theorem sum_3_164_2 : blockSum (rowCell 3) 164 2 ≤ (14024024287311088961822913 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_164) (by simpa only [blockSum_one] using cell_3_165) (by norm_num)

theorem sum_3_166_2 : blockSum (rowCell 3) 166 2 ≤ (618284694117661117662883 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_166) (by simpa only [blockSum_one] using cell_3_167) (by norm_num)

theorem sum_3_164_4 : blockSum (rowCell 3) 164 4 ≤ (26389718169664311315080573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_164_2 sum_3_166_2 (by norm_num)

theorem sum_3_160_8 : blockSum (rowCell 3) 160 8 ≤ (240775744440044847886420267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_160_4 sum_3_164_4 (by norm_num)

theorem sum_3_168_2 : blockSum (rowCell 3) 168 2 ≤ (43529504938702900316740399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_168) (by simpa only [blockSum_one] using cell_3_169) (by norm_num)

theorem sum_3_170_2 : blockSum (rowCell 3) 170 2 ≤ (38235168656497308111161711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_170) (by simpa only [blockSum_one] using cell_3_171) (by norm_num)

theorem sum_3_168_4 : blockSum (rowCell 3) 168 4 ≤ (8176467359520020842790211 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_168_2 sum_3_170_2 (by norm_num)

theorem sum_3_172_2 : blockSum (rowCell 3) 172 2 ≤ (33522053838994578579887589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_172) (by simpa only [blockSum_one] using cell_3_173) (by norm_num)

theorem sum_3_174_2 : blockSum (rowCell 3) 174 2 ≤ (14667987180357742460411361 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_174) (by simpa only [blockSum_one] using cell_3_175) (by norm_num)

theorem sum_3_172_4 : blockSum (rowCell 3) 172 4 ≤ (62858028199710063500710311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_172_2 sum_3_174_2 (by norm_num)

theorem sum_3_168_8 : blockSum (rowCell 3) 168 8 ≤ (144622701794910271928612421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_168_4 sum_3_172_4 (by norm_num)

theorem sum_3_160_16 : blockSum (rowCell 3) 160 16 ≤ (24087402889684694988439543 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_160_8 sum_3_168_8 (by norm_num)

theorem sum_3_176_2 : blockSum (rowCell 3) 176 2 ≤ (6406581528973853775841653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_176) (by simpa only [blockSum_one] using cell_3_177) (by norm_num)

theorem sum_3_178_2 : blockSum (rowCell 3) 178 2 ≤ (22346085060524563978385421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_178) (by simpa only [blockSum_one] using cell_3_179) (by norm_num)

theorem sum_3_176_4 : blockSum (rowCell 3) 176 4 ≤ (47972411176419979081752033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_176_2 sum_3_178_2 (by norm_num)

theorem sum_3_180_2 : blockSum (rowCell 3) 180 2 ≤ (3890351515470932562901 / 200000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_180) (by simpa only [blockSum_one] using cell_3_181) (by norm_num)

theorem sum_3_182_2 : blockSum (rowCell 3) 182 2 ≤ (16903291968400002821373033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_182) (by simpa only [blockSum_one] using cell_3_183) (by norm_num)

theorem sum_3_180_4 : blockSum (rowCell 3) 180 4 ≤ (36355049545754665635878033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_180_2 sum_3_182_2 (by norm_num)

theorem sum_3_176_8 : blockSum (rowCell 3) 176 8 ≤ (42163730361087322358815033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_176_4 sum_3_180_4 (by norm_num)

theorem sum_3_184_2 : blockSum (rowCell 3) 184 2 ≤ (366598976396238238388291 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_184) (by simpa only [blockSum_one] using cell_3_185) (by norm_num)

theorem sum_3_186_2 : blockSum (rowCell 3) 186 2 ≤ (3175052257770721536191993 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_186) (by simpa only [blockSum_one] using cell_3_187) (by norm_num)

theorem sum_3_184_4 : blockSum (rowCell 3) 184 4 ≤ (6841042021733103920074903 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_184_2 sum_3_186_2 (by norm_num)

theorem sum_3_188_2 : blockSum (rowCell 3) 188 2 ≤ (10981510855791744809547687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_188) (by simpa only [blockSum_one] using cell_3_189) (by norm_num)

theorem sum_3_190_2 : blockSum (rowCell 3) 190 2 ≤ (1896035941498990633503521 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_190) (by simpa only [blockSum_one] using cell_3_191) (by norm_num)

theorem sum_3_188_4 : blockSum (rowCell 3) 188 4 ≤ (5115422640821674494266323 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_188_2 sum_3_190_2 (by norm_num)

theorem sum_3_184_8 : blockSum (rowCell 3) 184 8 ≤ (5978232331277389207170613 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_184_4 sum_3_188_4 (by norm_num)

theorem sum_3_176_16 : blockSum (rowCell 3) 176 16 ≤ (13215331937239375837499497 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_176_8 sum_3_184_8 (by norm_num)

theorem sum_3_160_32 : blockSum (rowCell 3) 160 32 ≤ (258775882803674439095013829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_160_16 sum_3_176_16 (by norm_num)

#print axioms sum_3_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
