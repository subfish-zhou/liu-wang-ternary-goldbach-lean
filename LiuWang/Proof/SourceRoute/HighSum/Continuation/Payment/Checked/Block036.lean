import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_128_0 : expNegUpper (599455472021945108563 / 8145908344958596000 : ℝ) ≤ (686571386232557178742102367 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444247 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_128_1 : expNegUpper (76780421918833782726543 / 1042676268154700288000 : ℝ) ≤ (2617394187752111224126431543 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355531 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_128 : rowCell 2 128 ≤ (1564497380152824240594339349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (686571386232557178742102367 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2617394187752111224126431543 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_128_1
  · norm_num [gridPoint]

theorem exp_2_129_0 : expNegUpper (3091577974004958493983 / 41983553629987328000 : ℝ) ≤ (2093914236530285223268284593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355531 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_129_1 : expNegUpper (1546811579843141047391 / 20991776814993664000 : ℝ) ≤ (997177991053835386397491989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444583 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_129 : rowCell 2 129 ≤ (1490601686991771543857618787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2093914236530285223268284593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (997177991053835386397491989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_129_1
  · norm_num [gridPoint]

theorem exp_2_130_0 : expNegUpper (12975271006373890546877 / 176087375275070208000 : ℝ) ≤ (155808979319606075185956741 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444583 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_130_1 : expNegUpper (25967922384354754466807 / 352174750550140416000 : ℝ) ≤ (593224891883121547944018779 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (889509 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_130 : rowCell 2 130 ≤ (709643320944545234901329137 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155808979319606075185956741 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (593224891883121547944018779 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_130_1
  · norm_num [gridPoint]

theorem exp_2_131_0 : expNegUpper (11202405782215109060027 / 151926071550987776000 : ℝ) ≤ (9491593353175619477210696623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (889509 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_131_1 : expNegUpper (560499974242100446773 / 7596303577549388800 : ℝ) ≤ (4514418726950969301418589571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_131 : rowCell 2 131 ≤ (337631613475412192235169661 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9491593353175619477210696623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4514418726950969301418589571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_131_1
  · norm_num [gridPoint]

theorem exp_2_132_0 : expNegUpper (3949255132712493474771 / 53523179418458137600 : ℝ) ≤ (9028832837578470571440066517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_132_1 : expNegUpper (79039276706985096542011 / 1070463588369162752000 : ℝ) ≤ (343330839843361293421343399 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27819 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_132 : rowCell 2 132 ≤ (1284290434925207768131474151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9028832837578470571440066517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (343330839843361293421343399 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_132_1
  · norm_num [gridPoint]

theorem exp_2_133_0 : expNegUpper (26518807522271436078673 / 359155838062388736000 : ℝ) ≤ (8583266664533481795375383241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27819 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_133_1 : expNegUpper (13268603014112668685143 / 179577919031194368000 : ℝ) ≤ (8154643243051176100095220627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_133 : rowCell 2 133 ≤ (305135857106751462332198599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8583266664533481795375383241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8154643243051176100095220627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_133_1
  · norm_num [gridPoint]

theorem exp_2_134_0 : expNegUpper (1602616204110754527421 / 21689885566218496000 : ℝ) ≤ (65237113448391064341057157 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_134_1 : expNegUpper (3207481220772218239353 / 43379771132436992000 : ℝ) ≤ (7742672171013397980921110837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_134 : rowCell 2 134 ≤ (1159246226533049400693110487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65237113448391064341057157 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7742672171013397980921110837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_134_1
  · norm_num [gridPoint]

theorem exp_2_135_0 : expNegUpper (80708275562758770629577 / 1091543880740438528000 : ℝ) ≤ (1935667090989805996598303437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1781851 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_135_1 : expNegUpper (10095690500401509361247 / 136442985092554816000 : ℝ) ≤ (1469410422317542477474773239 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_135 : rowCell 2 135 ≤ (34386124195238198424241993 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1935667090989805996598303437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1469410422317542477474773239 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_135_1
  · norm_num [gridPoint]

theorem exp_2_136_0 : expNegUpper (3387034526284003655861 / 45775680061487808000 : ℝ) ≤ (3673524272747929354252455399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_136_1 : expNegUpper (216925622743292041489 / 2929643523935219712 : ℝ) ≤ (87093204733066032517656587 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44583 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_136 : rowCell 2 136 ≤ (1043826559756389807375825191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3673524272747929354252455399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87093204733066032517656587 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_136_1
  · norm_num [gridPoint]

theorem exp_2_137_0 : expNegUpper (654979835216386595467 / 8845692804133851136 : ℝ) ≤ (3483726520066424007487558903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44583 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_137_1 : expNegUpper (40965897044105712359043 / 552855800258365696000 : ℝ) ≤ (3301769895469191666332175481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1784067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_137 : rowCell 2 137 ≤ (494804494965292927714641979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3483726520066424007487558903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3301769895469191666332175481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_137_1
  · norm_num [gridPoint]

theorem exp_2_138_0 : expNegUpper (5889945562056723388341 / 79487836990250752000 : ℝ) ≤ (1650884166803204277195184109 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1784067 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_138_1 : expNegUpper (11788512953425921299739 / 158975673980501504000 : ℝ) ≤ (625494108606444550018093941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223103 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_138 : rowCell 2 138 ≤ (468825875153792224743055321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1650884166803204277195184109 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (625494108606444550018093941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_138_1
  · norm_num [gridPoint]

theorem exp_2_139_0 : expNegUpper (1107321520311895246399 / 14932942313547264000 : ℝ) ≤ (6254938164910042520243398743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (223103 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_139_1 : expNegUpper (277035027594610784759 / 3733235578386816000 : ℝ) ≤ (1184257044463198033655563847 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_139 : rowCell 2 139 ≤ (887901148972221764535710809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6254938164910042520243398743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1184257044463198033655563847 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_139_1
  · norm_num [gridPoint]

theorem exp_2_140_0 : expNegUpper (20910529464545254822973 / 281783616868583552000 : ℝ) ≤ (1480320623019891705020769047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_140_1 : expNegUpper (83704556893755430435731 / 1127134467474334208000 : ℝ) ≤ (5602185565893749362777354709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1786361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_140 : rowCell 2 140 ≤ (42015082195162377572772033 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1480320623019891705020769047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5602185565893749362777354709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_140_1
  · norm_num [gridPoint]

theorem exp_2_141_0 : expNegUpper (84238259365499401601739 / 1134321099738378752000 : ℝ) ≤ (5602183015469630420507349133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1786361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_141_1 : expNegUpper (8430174651243668085133 / 113432109973837875200 : ℝ) ≤ (1324311490456149710503362917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (893571 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_141 : rowCell 2 141 ≤ (794796153480016985607119841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5602183015469630420507349133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1324311490456149710503362917 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_141_1
  · norm_num [gridPoint]

theorem exp_2_142_0 : expNegUpper (2827918284589531237951 / 38051019010272614400 : ℝ) ≤ (1324310895159759289293797599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (893571 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_142_1 : expNegUpper (28300695708921877801187 / 380510190102726144000 : ℝ) ≤ (5006062687725596209228608789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446983 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_142 : rowCell 2 142 ≤ (150265269993174909785691033 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1324310895159759289293797599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5006062687725596209228608789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_142_1
  · norm_num [gridPoint]

theorem exp_2_143_0 : expNegUpper (2756128882809008794559 / 37056867070443008000 : ℝ) ≤ (2503030232860369374201218107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446983 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_143_1 : expNegUpper (172390299857018013753 / 2316054191902688000 : ℝ) ≤ (4728226290290506528082185797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178873 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_143 : rowCell 2 143 ≤ (709832935896597359414436729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2503030232860369374201218107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4728226290290506528082185797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_143_1
  · norm_num [gridPoint]

theorem exp_2_144_0 : expNegUpper (215114024615045137023 / 2890045065912608000 : ℝ) ≤ (1182056054477003035020184601 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178873 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_144_1 : expNegUpper (3444490452468849273367 / 46240721054601728000 : ℝ) ≤ (4463323305046303053492133393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (357907 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_144 : rowCell 2 144 ≤ (335127951702403159091445269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1182056054477003035020184601 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4463323305046303053492133393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_144_1
  · norm_num [gridPoint]

theorem exp_2_145_0 : expNegUpper (4126400093659091923867 / 55395048183433728000 : ℝ) ≤ (4463321373210709372283197891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (357907 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_145_1 : expNegUpper (2064812258738694551683 / 27697524091716864000 : ℝ) ≤ (4210937860535308440937288869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1790349 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_145 : rowCell 2 145 ≤ (3953342353778374610174481 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4463321373210709372283197891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4210937860535308440937288869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_145_1
  · norm_num [gridPoint]

theorem exp_2_146_0 : expNegUpper (43633190860943273068207 / 585298417822464256000 : ℝ) ≤ (4210936060637237565933039177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1790349 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_146_1 : expNegUpper (17467031877466279912017 / 234119367128985702400 : ℝ) ≤ (3970653168625351140273048527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_146 : rowCell 2 146 ≤ (74576104655550141757948581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4210936060637237565933039177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3970653168625351140273048527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_146_1
  · norm_num [gridPoint]

theorem exp_2_147_0 : expNegUpper (17576311820698709748777 / 235584099548700774400 : ℝ) ≤ (3970651492504636211667528483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_147_1 : expNegUpper (21987851216244640932859 / 294480124435875968000 : ℝ) ≤ (3742052903137361798521569213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_147 : rowCell 2 147 ≤ (140604333478267488627644071 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3970651492504636211667528483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3742052903137361798521569213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_147_1
  · norm_num [gridPoint]

theorem exp_2_148_0 : expNegUpper (7374995342000048746057 / 98772249845652864000 : ℝ) ≤ (1871025671533084663377699689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_148_1 : expNegUpper (29523620430768436804601 / 395088999382611456000 : ℝ) ≤ (3524722469409333007144844111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792839 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_148 : rowCell 2 148 ≤ (529899675147810776147133869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1871025671533084663377699689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3524722469409333007144844111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_148_1
  · norm_num [gridPoint]

theorem exp_2_149_0 : expNegUpper (142594474745194082387 / 1908218138972672000 : ℝ) ≤ (3524721018075348842265144263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1792839 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_149_1 : expNegUpper (71354830929320229069 / 954109069486336000 : ℝ) ≤ (1659125083894934911309901337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358737 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_149 : rowCell 2 149 ≤ (124748901713804136456451141 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3524721018075348842265144263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1659125083894934911309901337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_149_1
  · norm_num [gridPoint]

theorem exp_2_150_0 : expNegUpper (44873188465534672545261 / 600014256936880384000 : ℝ) ≤ (10369527557123781178370379 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358737 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_150_1 : expNegUpper (89819446965352138227841 / 1200028513873760768000 : ℝ) ≤ (3122228254376228881742509529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_150 : rowCell 2 150 ≤ (469645374504183733815454289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10369527557123781178370379 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3122228254376228881742509529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_150_1
  · norm_num [gridPoint]

theorem exp_2_151_0 : expNegUpper (30124814914102787492563 / 402481176398452224000 : ℝ) ≤ (3122227000158530060984732753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_151_1 : expNegUpper (753738301631245940147 / 10062029409961305600 : ℝ) ≤ (293625390258350180336027479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8977 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_151 : rowCell 2 151 ≤ (441789870594385020842291073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3122227000158530060984732753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (293625390258350180336027479 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_151_1
  · norm_num [gridPoint]

theorem exp_2_152_0 : expNegUpper (325020571935007144223 / 4338862081509670400 : ℝ) ≤ (1468126368746620230411978123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8977 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_152_1 : expNegUpper (13011570906454436690673 / 173554483260386816000 : ℝ) ≤ (1379965034678142789964632301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_152 : rowCell 2 152 ≤ (25960672996231747985173569 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1468126368746620230411978123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1379965034678142789964632301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_152_1
  · norm_num [gridPoint]

theorem exp_2_153_0 : expNegUpper (91640333121888905533839 / 1222342074755813888000 : ℝ) ≤ (34499112344729607525508721 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_153_1 : expNegUpper (45858328702992708504059 / 611171037377906944000 : ℝ) ≤ (129643313500736207155286321 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359429 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_153 : rowCell 2 153 ≤ (390330639335677566770340463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34499112344729607525508721 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (129643313500736207155286321 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_153_1
  · norm_num [gridPoint]

theorem exp_2_154_0 : expNegUpper (615187824499384831073 / 8198837366631168000 : ℝ) ≤ (1296432633034194443929321501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359429 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_154_1 : expNegUpper (1231407858273349867559 / 16397674733262336000 : ℝ) ≤ (2434679265866176584411415723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_154 : rowCell 2 154 ≤ (14664522568128356967963967 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1296432633034194443929321501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2434679265866176584411415723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_154_1
  · norm_num [gridPoint]

theorem exp_2_155_0 : expNegUpper (92919291793197104492837 / 1237331973539291648000 : ℝ) ≤ (1217339167294816471963842729 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_155_1 : expNegUpper (23249450557766793185049 / 309332993384822912000 : ℝ) ≤ (2284993668814963508157335777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_155 : rowCell 2 155 ≤ (344162722818578732103164669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1217339167294816471963842729 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2284993668814963508157335777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_155_1
  · norm_num [gridPoint]

theorem exp_2_156_0 : expNegUpper (23390924367273922939641 / 311215295097415808000 : ℝ) ≤ (285624100668800742339681981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_156_1 : expNegUpper (18728661196004372351399 / 248972236077932646400 : ℝ) ≤ (2143442467268650740393549359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89991 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_156 : rowCell 2 156 ≤ (322925478751696856724509639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (285624100668800742339681981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2143442467268650740393549359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_156_1
  · norm_num [gridPoint]

theorem exp_2_157_0 : expNegUpper (6280760046329475545813 / 83494215036385996800 : ℝ) ≤ (2143441667047663798252671381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (89991 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_157_1 : expNegUpper (15715351768283992307731 / 208735537590964992000 : ℝ) ≤ (1004833738836552001863219307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_157 : rowCell 2 157 ≤ (37856056267754449773142349 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2143441667047663798252671381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1004833738836552001863219307 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_157_1
  · norm_num [gridPoint]

theorem exp_2_158_0 : expNegUpper (47431205731537537753897 / 629994054503835904000 : ℝ) ≤ (2009666736402480835298624479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_158_1 : expNegUpper (94944226112452095737433 / 1259988109007671808000 : ℝ) ≤ (941659863006495264752774109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45041 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_158 : rowCell 2 158 ≤ (28388007044436099832157459 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2009666736402480835298624479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (941659863006495264752774109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_158_1
  · norm_num [gridPoint]

theorem exp_2_159_0 : expNegUpper (545809941519046659711 / 7243347604430336000 : ℝ) ≤ (1883319039660979982398033719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45041 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_159_1 : expNegUpper (17071368300108023957 / 226354612638448000 : ℝ) ≤ (1764059763592343128010949071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1802561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_159 : rowCell 2 159 ≤ (132985069637562934559252517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1883319039660979982398033719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1764059763592343128010949071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_159_1
  · norm_num [gridPoint]

theorem sum_2_128_2 : blockSum (rowCell 2) 128 2 ≤ (381887383393074473056494767 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_128) (by simpa only [blockSum_one] using cell_2_129) (by norm_num)

theorem sum_2_130_2 : blockSum (rowCell 2) 130 2 ≤ (1384906547895369619371668459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_130) (by simpa only [blockSum_one] using cell_2_131) (by norm_num)

theorem sum_2_128_4 : blockSum (rowCell 2) 128 4 ≤ (2912456081467667511597647527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_128_2 sum_2_130_2 (by norm_num)

theorem sum_2_132_2 : blockSum (rowCell 2) 132 2 ≤ (2504833863352213617460268547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_132) (by simpa only [blockSum_one] using cell_2_133) (by norm_num)

theorem sum_2_134_2 : blockSum (rowCell 2) 134 2 ≤ (2259602200780671750268854263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_134) (by simpa only [blockSum_one] using cell_2_135) (by norm_num)

theorem sum_2_132_4 : blockSum (rowCell 2) 132 4 ≤ (476443606413288536772912281 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_132_2 sum_2_134_2 (by norm_num)

theorem sum_2_128_8 : blockSum (rowCell 2) 128 8 ≤ (1323668528383527548865552233 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_128_4 sum_2_132_4 (by norm_num)

theorem sum_2_136_2 : blockSum (rowCell 2) 136 2 ≤ (2033435549686975662805109149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_136) (by simpa only [blockSum_one] using cell_2_137) (by norm_num)

theorem sum_2_138_2 : blockSum (rowCell 2) 138 2 ≤ (1825552899279806214021821451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_138) (by simpa only [blockSum_one] using cell_2_139) (by norm_num)

theorem sum_2_136_4 : blockSum (rowCell 2) 136 4 ≤ (19294942244833909384134653 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_136_2 sum_2_138_2 (by norm_num)

theorem sum_2_140_2 : blockSum (rowCell 2) 140 2 ≤ (1635097797383264537062560501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_140) (by simpa only [blockSum_one] using cell_2_141) (by norm_num)

theorem sum_2_142_2 : blockSum (rowCell 2) 142 2 ≤ (730579642931235954171445947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_142) (by simpa only [blockSum_one] using cell_2_143) (by norm_num)

theorem sum_2_140_4 : blockSum (rowCell 2) 140 4 ≤ (619251416649147289081090479 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_140_2 sum_2_142_2 (by norm_num)

theorem sum_2_136_8 : blockSum (rowCell 2) 136 8 ≤ (1391049106442503664446476599 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_136_4 sum_2_140_4 (by norm_num)

theorem sum_2_128_16 : blockSum (rowCell 2) 128 16 ≤ (17544593759280738713156800859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_128_8 sum_2_136_8 (by norm_num)

theorem sum_2_144_2 : blockSum (rowCell 2) 144 2 ≤ (651395340004673127905403749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_144) (by simpa only [blockSum_one] using cell_2_145) (by norm_num)

theorem sum_2_146_2 : blockSum (rowCell 2) 146 2 ≤ (289756542789367772143541233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_146) (by simpa only [blockSum_one] using cell_2_147) (by norm_num)

theorem sum_2_144_4 : blockSum (rowCell 2) 144 4 ≤ (246181685116681734438497243 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_144_2 sum_2_146_2 (by norm_num)

theorem sum_2_148_2 : blockSum (rowCell 2) 148 2 ≤ (1028895282003027321972938433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_148) (by simpa only [blockSum_one] using cell_2_149) (by norm_num)

theorem sum_2_150_2 : blockSum (rowCell 2) 150 2 ≤ (455717622549284377328872681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_150) (by simpa only [blockSum_one] using cell_2_151) (by norm_num)

theorem sum_2_148_4 : blockSum (rowCell 2) 148 4 ≤ (388066105420319215326136759 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_148_2 sum_2_150_2 (by norm_num)

theorem sum_2_144_8 : blockSum (rowCell 2) 144 8 ≤ (176085895130736536840626249 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_144_4 sum_2_148_4 (by norm_num)

theorem sum_2_152_2 : blockSum (rowCell 2) 152 2 ≤ (805701407275385534533117567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_152) (by simpa only [blockSum_one] using cell_2_153) (by norm_num)

theorem sum_2_154_2 : blockSum (rowCell 2) 154 2 ≤ (177693946755446914075565961 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_154) (by simpa only [blockSum_one] using cell_2_155) (by norm_num)

theorem sum_2_152_4 : blockSum (rowCell 2) 152 4 ≤ (1516477194297173190835381411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_152_2 sum_2_154_2 (by norm_num)

theorem sum_2_156_2 : blockSum (rowCell 2) 156 2 ≤ (625773928893732454909648431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_156) (by simpa only [blockSum_one] using cell_2_157) (by norm_num)

theorem sum_2_158_2 : blockSum (rowCell 2) 158 2 ≤ (68731276214935858430009953 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_158) (by simpa only [blockSum_one] using cell_2_159) (by norm_num)

theorem sum_2_156_4 : blockSum (rowCell 2) 156 4 ≤ (235124827722643864469945611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_156_2 sum_2_158_2 (by norm_num)

theorem sum_2_152_8 : blockSum (rowCell 2) 152 8 ≤ (1346050666455196256592554733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_152_4 sum_2_156_4 (by norm_num)

theorem sum_2_144_16 : blockSum (rowCell 2) 144 16 ≤ (7094248711178805934200765691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_144_8 sum_2_152_8 (by norm_num)

theorem sum_2_128_32 : blockSum (rowCell 2) 128 32 ≤ (492776849409190892947151331 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_128_16 sum_2_144_16 (by norm_num)

#print axioms sum_2_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
