import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_128_0 : expNegUpper (631023112135097108563 / 8145908344958596000 : ℝ) ≤ (113963259895585691573032023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183161 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_128_1 : expNegUpper (80807730007063670726543 / 1042676268154700288000 : ℝ) ≤ (55007103292303334009703213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366423 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_128 : rowCell 6 128 ≤ (32665276170981335318607367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113963259895585691573032023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55007103292303334009703213 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_128_1
  · norm_num [gridPoint]

theorem exp_6_129_0 : expNegUpper (3253738285234439453983 / 41983553629987328000 : ℝ) ≤ (27503535102513177573791913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366423 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_129_1 : expNegUpper (1627624738532810167391 / 20991776814993664000 : ℝ) ≤ (414549292734791804528123 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183263 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_129 : rowCell 6 129 ≤ (31522065037960456000870799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27503535102513177573791913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (414549292734791804528123 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_129_1
  · norm_num [gridPoint]

theorem exp_6_130_0 : expNegUpper (40959491832616967640631 / 528262125825210624000 : ℝ) ≤ (212249111883733659910095829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183263 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_130_1 : expNegUpper (81957774933801287400421 / 1056524251650421248000 : ℝ) ≤ (204597516001206551599458279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458289 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_130 : rowCell 6 130 ≤ (7599207654003020149811991 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (212249111883733659910095829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (204597516001206551599458279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_130_1
  · norm_num [gridPoint]

theorem exp_6_131_0 : expNegUpper (82497547948749923420189 / 1063482500856914432000 : ℝ) ≤ (51149349033423940473314339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458289 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_131_1 : expNegUpper (4126867701044232727411 / 53174125042845721600 : ℝ) ≤ (24635109930617109527579259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458423 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_131 : rowCell 6 131 ≤ (29290740738019607149025769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51149349033423940473314339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24635109930617109527579259 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_131_1
  · norm_num [gridPoint]

theorem exp_6_132_0 : expNegUpper (4153957998687379874771 / 53523179418458137600 : ℝ) ≤ (49270191371184779043479137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458423 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_132_1 : expNegUpper (83119984180229256542011 / 1070463588369162752000 : ℝ) ≤ (94853111517521837590433657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_132 : rowCell 6 132 ≤ (1762803419174847461746403 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49270191371184779043479137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (94853111517521837590433657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_132_1
  · norm_num [gridPoint]

theorem exp_6_133_0 : expNegUpper (83663829732565604236019 / 1077467514187166208000 : ℝ) ≤ (11856632172685776036430987 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_133_1 : expNegUpper (41852837702086870055429 / 538733757093583104000 : ℝ) ≤ (182479721037971318147481889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366959 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_133 : rowCell 6 133 ≤ (27140125532316669546925813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11856632172685776036430987 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (182479721037971318147481889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_133_1
  · norm_num [gridPoint]

theorem exp_6_134_0 : expNegUpper (1685031344350851807421 / 21689885566218496000 : ℝ) ≤ (182479618237735294637654053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366959 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_134_1 : expNegUpper (3371777507402270079353 / 43379771132436992000 : ℝ) ≤ (175406845839095868132039679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917681 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_134 : rowCell 6 134 ≤ (6524350624775649354290967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (182479618237735294637654053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (175406845839095868132039679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_134_1
  · norm_num [gridPoint]

theorem exp_6_135_0 : expNegUpper (84842382421017202629577 / 1091543880740438528000 : ℝ) ≤ (175406748297685724658082021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917681 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_135_1 : expNegUpper (10610785126902117361247 / 136442985092554816000 : ℝ) ≤ (10530774282943718753295333 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917969 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_135 : rowCell 6 135 ≤ (25077434029144079603887399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (175406748297685724658082021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10530774282943718753295333 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_135_1
  · norm_num [gridPoint]

theorem exp_6_136_0 : expNegUpper (10679535666916010967583 / 137327040184463424000 : ℝ) ≤ (168492296035136378202696139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917969 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_136_1 : expNegUpper (683849723095943580467 / 8788930571805659136 : ℝ) ≤ (80870240577720376402755853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73461 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_136 : rowCell 6 136 ≤ (24080870806247641552259657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (168492296035136378202696139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80870240577720376402755853 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_136_1
  · norm_num [gridPoint]

theorem exp_6_137_0 : expNegUpper (688266287622511139467 / 8845692804133851136 : ℝ) ≤ (3234807870149761508706077 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73461 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_137_1 : expNegUpper (43039625396361712359043 / 552855800258365696000 : ℝ) ≤ (77577310227913396865540829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_137 : rowCell 6 137 ≤ (11554134564284513962657799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3234807870149761508706077 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77577310227913396865540829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_137_1
  · norm_num [gridPoint]

theorem exp_6_138_0 : expNegUpper (43316697132906631718387 / 556414858931755264000 : ℝ) ≤ (77577268725333303476075841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918561 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_138_1 : expNegUpper (86680397224747017098173 / 1112829717863510528000 : ℝ) ≤ (74368846392874120477504437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57429 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_138 : rowCell 6 138 ≤ (4432018891402994747671013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (77577268725333303476075841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (74368846392874120477504437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_138_1
  · norm_num [gridPoint]

theorem exp_6_139_0 : expNegUpper (3489464810666593899197 / 44798826940641792000 : ℝ) ≤ (148737614226623550054805941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57429 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_139_1 : expNegUpper (872846646754023714277 / 11199706735160448000 : ℝ) ≤ (1139936000801963347069337 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229793 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_139 : rowCell 6 139 ≤ (663647660260059592964759 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148737614226623550054805941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1139936000801963347069337 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_139_1
  · norm_num [gridPoint]

theorem exp_6_140_0 : expNegUpper (21960743486926822822973 / 281783616868583552000 : ℝ) ≤ (142491925795070017486082203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229793 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_140_1 : expNegUpper (87892063137028134435731 / 1127134467474334208000 : ℝ) ≤ (136419286746998728685446131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183897 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_140 : rowCell 6 140 ≤ (4067691240572034247143397 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (142491925795070017486082203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (136419286746998728685446131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_140_1
  · norm_num [gridPoint]

theorem exp_6_141_0 : expNegUpper (88452465301279241601739 / 1134321099738378752000 : ℝ) ≤ (68209608254268036411607799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (183897 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_141_1 : expNegUpper (8850260260196295285133 / 113432109973837875200 : ℝ) ≤ (8157547930840086667670459 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367921 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_141 : rowCell 6 141 ≤ (3893100683712706812259427 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68209608254268036411607799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8157547930840086667670459 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_141_1
  · norm_num [gridPoint]

theorem exp_6_142_0 : expNegUpper (8906510431971934513853 / 114153057030817843200 : ℝ) ≤ (65260350269727045189660141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367921 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_142_1 : expNegUpper (89116293062545473403561 / 1141530570308178432000 : ℝ) ≤ (124797152404751899813835069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_142 : rowCell 6 142 ≤ (18618007223825005364954203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65260350269727045189660141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124797152404751899813835069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_142_1
  · norm_num [gridPoint]

theorem exp_6_143_0 : expNegUpper (2892932290173104794559 / 37056867070443008000 : ℝ) ≤ (62398544879061734603937997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_143_1 : expNegUpper (180913597804666013753 / 2316054191902688000 : ℝ) ≤ (119248681002174523723173567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_143 : rowCell 6 143 ≤ (8898018431856548549880079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62398544879061734603937997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119248681002174523723173567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_143_1
  · norm_num [gridPoint]

theorem exp_6_144_0 : expNegUpper (11881561226389289317 / 152107635048032000 : ℝ) ≤ (23849724378200988134138611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_144_1 : expNegUpper (190217193557912016493 / 2433722160768512000 : ℝ) ≤ (1138751445420234044137229 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841567 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_144 : rowCell 6 144 ≤ (16999594495430331597459399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23849724378200988134138611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1138751445420234044137229 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_144_1
  · norm_num [gridPoint]

theorem exp_6_145_0 : expNegUpper (90922007287635042401207 / 1163296011852108288000 : ℝ) ≤ (22775017759940036365634043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841567 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_145_1 : expNegUpper (45488185170782857585343 / 581648005926054144000 : ℝ) ≤ (21735183453368493275331209 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_145 : rowCell 6 145 ≤ (4057154827635450704126607 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22775017759940036365634043 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21735183453368493275331209 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_145_1
  · norm_num [gridPoint]

theorem exp_6_146_0 : expNegUpper (45773668444467113068207 / 585298417822464256000 : ℝ) ≤ (108675864732088785260197779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_146_1 : expNegUpper (18320552941625102312017 / 234119367128985702400 : ℝ) ≤ (103649983891418147125464811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_146 : rowCell 6 146 ≤ (7741495821565374095786041 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (108675864732088785260197779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (103649983891418147125464811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_146_1
  · norm_num [gridPoint]

theorem exp_6_147_0 : expNegUpper (18435172823358959348777 / 235584099548700774400 : ℝ) ≤ (103649934408319668237926073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842921 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_147_1 : expNegUpper (23058090008006560932859 / 294480124435875968000 : ℝ) ≤ (98795967397583467634272099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_147 : rowCell 6 147 ≤ (7381268522338180204449663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (103649934408319668237926073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98795967397583467634272099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_147_1
  · norm_num [gridPoint]

theorem exp_6_148_0 : expNegUpper (23201899740888850238171 / 296316749536958592000 : ℝ) ≤ (2469898020389884636149 / 25000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_148_1 : expNegUpper (92865166305606558413803 / 1185266998147834368000 : ℝ) ≤ (47056078211462634427895637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1844311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_148 : rowCell 6 148 ≤ (14067030308083570095084053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2469898020389884636149 / 25000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47056078211462634427895637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_148_1
  · norm_num [gridPoint]

theorem exp_6_149_0 : expNegUpper (149508082274487496787 / 1908218138972672000 : ℝ) ≤ (47056056298430571608657741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1844311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_149_1 : expNegUpper (74800954816964081869 / 954109069486336000 : ℝ) ≤ (22399133034883830111997527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92251 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_149 : rowCell 6 149 ≤ (3349049856228383871667977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47056056298430571608657741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22399133034883830111997527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_149_1
  · norm_num [gridPoint]

theorem exp_6_150_0 : expNegUpper (47040365741565648545261 / 600014256936880384000 : ℝ) ≤ (89596490929539183131570411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92251 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_150_1 : expNegUpper (94140451671160522227841 / 1200028513873760768000 : ℝ) ≤ (5327924658110120807298961 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_150 : rowCell 6 150 ≤ (1593716182682064652886551 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (89596490929539183131570411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5327924658110120807298961 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_150_1
  · norm_num [gridPoint]

theorem exp_6_151_0 : expNegUpper (94722149140623882477689 / 1207443529195356672000 : ℝ) ≤ (85246755801265122650691901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_151_1 : expNegUpper (2369573768695286620441 / 30186088229883916800 : ℝ) ≤ (81060387976460999826470809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_151 : rowCell 6 151 ≤ (3031816585211569162961967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (85246755801265122650691901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81060387976460999826470809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_151_1
  · norm_num [gridPoint]

theorem exp_6_152_0 : expNegUpper (2384170359659277209561 / 30372034570567692800 : ℝ) ≤ (81060351600125131429186541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_152_1 : expNegUpper (95428700743496576834711 / 1214881382822707712000 : ℝ) ≤ (77034526095461004243311827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923599 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_152 : rowCell 6 152 ≤ (230568410398576412828147 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81060351600125131429186541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77034526095461004243311827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_152_1
  · norm_num [gridPoint]

theorem exp_6_153_0 : expNegUpper (96014737212711561533839 / 1222342074755813888000 : ℝ) ≤ (19258622986777106424244017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923599 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_153_1 : expNegUpper (48038855825277252504059 / 611171037377906944000 : ℝ) ≤ (73166215747799762718897607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_153 : rowCell 6 153 ≤ (10952770551061024743361039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19258622986777106424244017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73166215747799762718897607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_153_1
  · norm_num [gridPoint]

theorem exp_6_154_0 : expNegUpper (1933318552239678973219 / 24596512099893504000 : ℝ) ≤ (2286443240885399974675553 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923971 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_154_1 : expNegUpper (3869199738452955842677 / 49193024199787008000 : ℝ) ≤ (277809120714891832946629 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_154 : rowCell 6 154 ≤ (1299983315052531794772629 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2286443240885399974675553 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (277809120714891832946629 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_154_1
  · norm_num [gridPoint]

theorem exp_6_155_0 : expNegUpper (97320395576526896492837 / 1237331973539291648000 : ℝ) ≤ (6945225013403318479435229 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924347 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_155_1 : expNegUpper (24346389042035849185049 / 309332993384822912000 : ℝ) ≤ (65889381239423996127060703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369891 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_155 : rowCell 6 155 ≤ (493461667787471736161271 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6945225013403318479435229 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65889381239423996127060703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_155_1
  · norm_num [gridPoint]

theorem exp_6_156_0 : expNegUpper (24494537774669762939641 / 311215295097415808000 : ℝ) ≤ (13177870616058544367366131 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369891 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_156_1 : expNegUpper (19608881952670330751399 / 248972236077932646400 : ℝ) ≤ (12494808131205193178305549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115639 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_156 : rowCell 6 156 ≤ (9360373997738918682972901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13177870616058544367366131 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12494808131205193178305549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_156_1
  · norm_num [gridPoint]

theorem exp_6_157_0 : expNegUpper (19727840834155812237439 / 250482645109157990400 : ℝ) ≤ (62474014278017051593436193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115639 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_157_1 : expNegUpper (49353282119643656923193 / 626206612772894976000 : ℝ) ≤ (11840532063668015728513407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_157 : rowCell 6 157 ≤ (1109096553806711825177319 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62474014278017051593436193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11840532063668015728513407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_157_1
  · norm_num [gridPoint]

theorem exp_6_158_0 : expNegUpper (49651782392582785753897 / 629994054503835904000 : ℝ) ≤ (2368105424867445984540039 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_158_1 : expNegUpper (99372029588289023737433 / 1259988109007671808000 : ℝ) ≤ (28035770784233525125248791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462947 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_158 : rowCell 6 158 ≤ (4202948283674770306174139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2368105424867445984540039 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28035770784233525125248791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_158_1
  · norm_num [gridPoint]

theorem exp_6_159_0 : expNegUpper (3998849717367089177977 / 50703433231012352000 : ℝ) ≤ (56071518457950103512020219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462947 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_159_1 : expNegUpper (125051019753369287699 / 1584482288469136000 : ℝ) ≤ (53076903476329876650803047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (926291 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_159 : rowCell 6 159 ≤ (7959200990483027733142751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56071518457950103512020219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53076903476329876650803047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_159_1
  · norm_num [gridPoint]

theorem sum_6_128_2 : blockSum (rowCell 6) 128 2 ≤ (32093670604470895659739083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_128) (by simpa only [blockSum_one] using cell_6_129) (by norm_num)

theorem sum_6_130_2 : blockSum (rowCell 6) 130 2 ≤ (59687571354031687748273733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_130) (by simpa only [blockSum_one] using cell_6_131) (by norm_num)

theorem sum_6_128_4 : blockSum (rowCell 6) 128 4 ≤ (123874912562973479067751899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_128_2 sum_6_130_2 (by norm_num)

theorem sum_6_132_2 : blockSum (rowCell 6) 132 2 ≤ (55344980239114228934868261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_132) (by simpa only [blockSum_one] using cell_6_133) (by norm_num)

theorem sum_6_134_2 : blockSum (rowCell 6) 134 2 ≤ (51174836528246677021051267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_134) (by simpa only [blockSum_one] using cell_6_135) (by norm_num)

theorem sum_6_132_4 : blockSum (rowCell 6) 132 4 ≤ (13314977095920113244489941 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_132_2 sum_6_134_2 (by norm_num)

theorem sum_6_128_8 : blockSum (rowCell 6) 128 8 ≤ (230394729330334385023671427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_128_4 sum_6_132_4 (by norm_num)

theorem sum_6_136_2 : blockSum (rowCell 6) 136 2 ≤ (9437827986963333895515051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_136) (by simpa only [blockSum_one] using cell_6_137) (by norm_num)

theorem sum_6_138_2 : blockSum (rowCell 6) 138 2 ≤ (43396819585336880713227353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_138) (by simpa only [blockSum_one] using cell_6_139) (by norm_num)

theorem sum_6_136_4 : blockSum (rowCell 6) 136 4 ≤ (5661622470009596886925163 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_136_2 sum_6_138_2 (by norm_num)

theorem sum_6_140_2 : blockSum (rowCell 6) 140 2 ≤ (995098990535592632425353 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_140) (by simpa only [blockSum_one] using cell_6_141) (by norm_num)

theorem sum_6_142_2 : blockSum (rowCell 6) 142 2 ≤ (36414044087538102464714361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_142) (by simpa only [blockSum_one] using cell_6_143) (by norm_num)

theorem sum_6_140_4 : blockSum (rowCell 6) 140 4 ≤ (76218003708961807761728481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_140_2 sum_6_142_2 (by norm_num)

theorem sum_6_136_8 : blockSum (rowCell 6) 136 8 ≤ (166803963229115357952531089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_136_4 sum_6_140_4 (by norm_num)

theorem sum_6_128_16 : blockSum (rowCell 6) 128 16 ≤ (99299673139862435744050629 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_128_8 sum_6_136_8 (by norm_num)

theorem sum_6_144_2 : blockSum (rowCell 6) 144 2 ≤ (33228213805972134413965827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_144) (by simpa only [blockSum_one] using cell_6_145) (by norm_num)

theorem sum_6_146_2 : blockSum (rowCell 6) 146 2 ≤ (1890345542987944287529463 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_146) (by simpa only [blockSum_one] using cell_6_147) (by norm_num)

theorem sum_6_144_4 : blockSum (rowCell 6) 144 4 ≤ (12694748498755848602887447 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_144_2 sum_6_146_2 (by norm_num)

theorem sum_6_148_2 : blockSum (rowCell 6) 148 2 ≤ (27463229732997105581755961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_148) (by simpa only [blockSum_one] using cell_6_149) (by norm_num)

theorem sum_6_150_2 : blockSum (rowCell 6) 150 2 ≤ (6219248950575698468735069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_150) (by simpa only [blockSum_one] using cell_6_151) (by norm_num)

theorem sum_6_148_4 : blockSum (rowCell 6) 148 4 ≤ (52340225535299899456696237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_148_2 sum_6_150_2 (by norm_num)

theorem sum_6_144_8 : blockSum (rowCell 6) 144 8 ≤ (3619186500908723202222921 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_144_4 sum_6_148_4 (by norm_num)

theorem sum_6_152_2 : blockSum (rowCell 6) 152 2 ≤ (22481191070989845384768389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_152) (by simpa only [blockSum_one] using cell_6_153) (by norm_num)

theorem sum_6_154_2 : blockSum (rowCell 6) 154 2 ≤ (5067274969042422270351613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_154) (by simpa only [blockSum_one] using cell_6_155) (by norm_num)

theorem sum_6_152_4 : blockSum (rowCell 6) 152 4 ≤ (42750290947159534466174841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_152_2 sum_6_154_2 (by norm_num)

theorem sum_6_156_2 : blockSum (rowCell 6) 156 2 ≤ (18233146428192613284391453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_156) (by simpa only [blockSum_one] using cell_6_157) (by norm_num)

theorem sum_6_158_2 : blockSum (rowCell 6) 158 2 ≤ (16365097557832568345491029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_158) (by simpa only [blockSum_one] using cell_6_159) (by norm_num)

theorem sum_6_156_4 : blockSum (rowCell 6) 156 4 ≤ (17299121993012590814941241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_156_2 sum_6_158_2 (by norm_num)

theorem sum_6_152_8 : blockSum (rowCell 6) 152 8 ≤ (77348534933184716096057323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_152_4 sum_6_156_4 (by norm_num)

theorem sum_6_144_16 : blockSum (rowCell 6) 144 16 ≤ (38632500592452771713438159 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_144_8 sum_6_152_8 (by norm_num)

theorem sum_6_128_32 : blockSum (rowCell 6) 128 32 ≤ (590361195521713601543393311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_128_16 sum_6_144_16 (by norm_num)

#print axioms sum_6_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
