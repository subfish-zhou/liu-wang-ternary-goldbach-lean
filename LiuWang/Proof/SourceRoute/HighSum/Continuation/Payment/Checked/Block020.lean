import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_128_0 : expNegUpper (582236759232953108563 / 8145908344958596000 : ℝ) ≤ (45475930085162437968272661889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436971 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_128_1 : expNegUpper (74583708416162934726543 / 1042676268154700288000 : ℝ) ≤ (43039979129491073524252459077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437159 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_128 : rowCell 1 128 ≤ (12909319251889438196598326773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45475930085162437968272661889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43039979129491073524252459077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_128_1
  · norm_num [gridPoint]

theorem exp_1_129_0 : expNegUpper (3003126895152514333983 / 41983553629987328000 : ℝ) ≤ (2689997367081619589558680979 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437159 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_129_1 : expNegUpper (1502731675103321527391 / 20991776814993664000 : ℝ) ≤ (81420284988495131334716338919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437349 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_129 : rowCell 1 129 ≤ (3053566281516399334911270581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2689997367081619589558680979 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81420284988495131334716338919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_129_1
  · norm_num [gridPoint]

theorem exp_1_130_0 : expNegUpper (12605511222102018546877 / 176087375275070208000 : ℝ) ≤ (81420245304452224255131861243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437349 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_130_1 : expNegUpper (25230830060584386466807 / 352174750550140416000 : ℝ) ≤ (76967268007900834228357433393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (350033 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_130 : rowCell 1 130 ≤ (18479615635229242546907233 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81420245304452224255131861243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (76967268007900834228357433393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_130_1
  · norm_num [gridPoint]

theorem exp_1_131_0 : expNegUpper (76191000035554403420189 / 1063482500856914432000 : ℝ) ≤ (38483615492168476659715402909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (350033 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_131_1 : expNegUpper (3812571884413141527411 / 53174125042845721600 : ℝ) ≤ (18178788600340950261729037189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (875471 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_131 : rowCell 1 131 ≤ (10914974022593418973915520943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38483615492168476659715402909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18178788600340950261729037189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_131_1
  · norm_num [gridPoint]

theorem exp_1_132_0 : expNegUpper (3837599023998919074771 / 53523179418458137600 : ℝ) ≤ (72715119878671842063687339797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (875471 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_132_1 : expNegUpper (76813436267033736542011 / 1070463588369162752000 : ℝ) ≤ (68658085089732437753690039813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109483 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_132 : rowCell 1 132 ≤ (10309061121284878885003306947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72715119878671842063687339797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68658085089732437753690039813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_132_1
  · norm_num [gridPoint]

theorem exp_1_133_0 : expNegUpper (25772006219407564078673 / 359155838062388736000 : ℝ) ≤ (68658052916286865152946088651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109483 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_133_1 : expNegUpper (12896415985067420685143 / 179577919031194368000 : ℝ) ≤ (3239506096436508209441989789 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (876261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_133 : rowCell 1 133 ≤ (4865580402271614549795162977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68658052916286865152946088651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3239506096436508209441989789 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_133_1
  · norm_num [gridPoint]

theorem exp_1_134_0 : expNegUpper (1557662491252519647421 / 21689885566218496000 : ℝ) ≤ (64790091960622522602090159847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (876261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_134_1 : expNegUpper (3117865064428553599353 / 43379771132436992000 : ℝ) ≤ (7638159129037463845366146683 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1753323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_134 : rowCell 1 134 ≤ (918040312440087508554624867 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64790091960622522602090159847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7638159129037463845366146683 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_134_1
  · norm_num [gridPoint]

theorem exp_1_135_0 : expNegUpper (6034869860425146048429 / 83964913903110656000 : ℝ) ≤ (7638155641633862748703329527 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1753323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_135_1 : expNegUpper (754979215002887797019 / 10495614237888832000 : ℝ) ≤ (2879875817091913466004902071 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_135 : rowCell 1 135 ≤ (4327956006881319692806861037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7638155641633862748703329527 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2879875817091913466004902071 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_135_1
  · norm_num [gridPoint]

theorem exp_1_136_0 : expNegUpper (3292774146636003655861 / 45775680061487808000 : ℝ) ≤ (143993725955522515009191279 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_136_1 : expNegUpper (210912376404007049489 / 2929643523935219712 : ℝ) ≤ (339130134189650400832734347 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_136 : rowCell 1 136 ≤ (8156808597990224902532720533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (143993725955522515009191279 / 2500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (339130134189650400832734347 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_136_1
  · norm_num [gridPoint]

theorem exp_1_137_0 : expNegUpper (636823588449409571467 / 8845692804133851136 : ℝ) ≤ (27130398663972393422034711569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_137_1 : expNegUpper (39834772488329712359043 / 552855800258365696000 : ℝ) ≤ (51089169857832406910905066279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1755777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_137 : rowCell 1 137 ≤ (1920553564387004110077563501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27130398663972393422034711569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51089169857832406910905066279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_137_1
  · norm_num [gridPoint]

theorem exp_1_138_0 : expNegUpper (40091212644300935718387 / 556414858931755264000 : ℝ) ≤ (51089147416933831753908447877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1755777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_138_1 : expNegUpper (80250059828109321098173 / 1112829717863510528000 : ℝ) ≤ (12019143320201968080658045949 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1756611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_138 : rowCell 1 138 ≤ (7231253447481514438573599129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51089147416933831753908447877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12019143320201968080658045949 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_138_1
  · norm_num [gridPoint]

theorem exp_1_139_0 : expNegUpper (1076866929451730126399 / 14932942313547264000 : ℝ) ≤ (48076552432053221708214359447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1756611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_139_1 : expNegUpper (269445652327303264759 / 3733235578386816000 : ℝ) ≤ (5652136345517385072470202367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_139 : rowCell 1 139 ≤ (3401528140186950880930397599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (48076552432053221708214359447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5652136345517385072470202367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_139_1
  · norm_num [gridPoint]

theorem exp_1_140_0 : expNegUpper (20337685452337126822973 / 281783616868583552000 : ℝ) ≤ (45217071404278940670097326827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_140_1 : expNegUpper (81420462579243046435731 / 1127134467474334208000 : ℝ) ≤ (21252421974208459974562382267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_140 : rowCell 1 140 ≤ (1279352176035381368808189997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45217071404278940670097326827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21252421974208459974562382267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_140_1
  · norm_num [gridPoint]

theorem exp_1_141_0 : expNegUpper (81939601582346761601739 / 1134321099738378752000 : ℝ) ≤ (21252412990023782339135416071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_141_1 : expNegUpper (8201037046360416885133 / 113432109973837875200 : ℝ) ≤ (19967015484915709084620096831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43979 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_141 : rowCell 1 141 ≤ (6011515514945716336139156063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21252412990023782339135416071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19967015484915709084620096831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_141_1
  · norm_num [gridPoint]

theorem exp_1_142_0 : expNegUpper (2751053634007105637951 / 38051019010272614400 : ℝ) ≤ (39934014301137341737858417287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43979 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_142_1 : expNegUpper (27534476447870997801187 / 380510190102726144000 : ℝ) ≤ (18749469456412039035395610221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70401 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_142 : rowCell 1 142 ≤ (5646480517030969900909840917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39934014301137341737858417287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18749469456412039035395610221 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_142_1
  · norm_num [gridPoint]

theorem exp_1_143_0 : expNegUpper (2681508842428592794559 / 37056867070443008000 : ℝ) ≤ (18749461728662692742163612281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70401 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_143_1 : expNegUpper (167741228249210013753 / 2316054191902688000 : ℝ) ≤ (17596977449154802071718731191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_143 : rowCell 1 143 ≤ (5300829999700801084467594667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18749461728662692742163612281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17596977449154802071718731191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_143_1
  · norm_num [gridPoint]

theorem exp_1_144_0 : expNegUpper (209312767149762577023 / 2890045065912608000 : ℝ) ≤ (17596970287307411349773447261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_144_1 : expNegUpper (3351961602397133433367 / 46240721054601728000 : ℝ) ≤ (16506787936081187350474688093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1761777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_144 : rowCell 1 144 ≤ (4973753379489550885832477569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17596970287307411349773447261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16506787936081187350474688093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_144_1
  · norm_num [gridPoint]

theorem exp_1_145_0 : expNegUpper (28108872415469259467069 / 387765337284036096000 : ℝ) ≤ (33013562603727168299164724789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1761777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_145_1 : expNegUpper (14066935313485357861781 / 193882668642018048000 : ℝ) ≤ (15476208579988811378788272127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (352533 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_145 : rowCell 1 145 ≤ (233222835690214865869039419 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33013562603727168299164724789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15476208579988811378788272127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_145_1
  · norm_num [gridPoint]

theorem exp_1_146_0 : expNegUpper (42465657633566633068207 / 585298417822464256000 : ℝ) ≤ (30952404874869815426448673573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (352533 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_146_1 : expNegUpper (17001474933379649512017 / 234119367128985702400 : ℝ) ≤ (29005219854893563696586427203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44089 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_146 : rowCell 1 146 ≤ (4372163863472813752437650401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30952404874869815426448673573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29005219854893563696586427203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_146_1
  · norm_num [gridPoint]

theorem exp_1_147_0 : expNegUpper (17107842182884028148777 / 235584099548700774400 : ℝ) ≤ (5801041697112961740754108557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44089 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_147_1 : expNegUpper (21404084602556320932859 / 294480124435875968000 : ℝ) ≤ (13583428552773188782688367217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882231 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_147 : rowCell 1 147 ≤ (2048058744997003608351316571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5801041697112961740754108557 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13583428552773188782688367217 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_147_1
  · norm_num [gridPoint]

theorem exp_1_148_0 : expNegUpper (552245603721840057389 / 7597865372742528000 : ℝ) ≤ (27166846588610743759994647189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882231 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_148_1 : expNegUpper (2210987515467484677277 / 30391461490970112000 : ℝ) ≤ (12716169685535829351318828613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_148 : rowCell 1 148 ≤ (47944748715764705496670127 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27166846588610743759994647189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12716169685535829351318828613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_148_1
  · norm_num [gridPoint]

theorem exp_1_149_0 : expNegUpper (138823416092852219987 / 1908218138972672000 : ℝ) ≤ (1017293185883653847170034547 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_149_1 : expNegUpper (69475126990605400269 / 954109069486336000 : ℝ) ≤ (11898409354754477240738197233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1766289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_149 : rowCell 1 149 ≤ (448729215934533819657857067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1017293185883653847170034547 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11898409354754477240738197233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_149_1
  · norm_num [gridPoint]

theorem exp_1_150_0 : expNegUpper (43691091769517776545261 / 600014256936880384000 : ℝ) ≤ (951872388911491882978088887 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1766289 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_150_1 : expNegUpper (87462535307638474227841 / 1200028513873760768000 : ℝ) ≤ (1112779608252699360532208129 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_150 : rowCell 1 150 ≤ (839545630216551889368269567 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (951872388911491882978088887 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1112779608252699360532208129 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_150_1
  · norm_num [gridPoint]

theorem exp_1_151_0 : expNegUpper (29334323205318147492563 / 402481176398452224000 : ℝ) ≤ (22255583863435849534295023619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_151_1 : expNegUpper (734036690030964340147 / 10062029409961305600 : ℝ) ≤ (2600513039797242543165324531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110509 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_151 : rowCell 1 151 ≤ (313995114865646240634856181 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22255583863435849534295023619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2600513039797242543165324531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_151_1
  · norm_num [gridPoint]

theorem exp_1_152_0 : expNegUpper (2215675082028198809561 / 30372034570567692800 : ℝ) ≤ (325064010204024560693208887 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110509 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_152_1 : expNegUpper (88709521218827136834711 / 1214881382822707712000 : ℝ) ≤ (9718974531367339070659075821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_152 : rowCell 1 152 ≤ (2934486128558518653972474759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (325064010204024560693208887 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9718974531367339070659075821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_152_1
  · norm_num [gridPoint]

theorem exp_1_153_0 : expNegUpper (89254294526894729533839 / 1222342074755813888000 : ℝ) ≤ (4859485497017761513523290167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769083 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_153_1 : expNegUpper (44668950272655684504059 / 611171037377906944000 : ℝ) ≤ (4538217666710688667510516683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442507 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_153 : rowCell 1 153 ≤ (2741155831792058997921778873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4859485497017761513523290167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4538217666710688667510516683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_153_1
  · norm_num [gridPoint]

theorem exp_1_154_0 : expNegUpper (599232355637289471073 / 8198837366631168000 : ℝ) ≤ (18152864140182340273182428621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1770029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_154_1 : expNegUpper (1199594010340094187559 / 16397674733262336000 : ℝ) ≤ (847238209179758701210876631 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1770981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_154 : rowCell 1 154 ≤ (319918823799412935803363343 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18152864140182340273182428621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (847238209179758701210876631 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_154_1
  · norm_num [gridPoint]

theorem exp_1_155_0 : expNegUpper (90518689729562672492837 / 1237331973539291648000 : ℝ) ≤ (16944758165102185157646501059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1770981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_155_1 : expNegUpper (22651120475438217185049 / 309332993384822912000 : ℝ) ≤ (7904837630774735892818134741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1771941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_155 : rowCell 1 155 ≤ (2388482713282720581652214609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16944758165102185157646501059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7904837630774735892818134741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_155_1
  · norm_num [gridPoint]

theorem exp_1_156_0 : expNegUpper (22788953417785282939641 / 311215295097415808000 : ℝ) ≤ (1580966971404339418461650811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1771941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_156_1 : expNegUpper (18248540783277485951399 / 248972236077932646400 : ℝ) ≤ (1842974926739363999597739149 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772907 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_156 : rowCell 1 156 ≤ (556996604798284834197070683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1580966971404339418461650811 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1842974926739363999597739149 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_156_1
  · norm_num [gridPoint]

theorem exp_1_157_0 : expNegUpper (6119749010844496345813 / 83494215036385996800 : ℝ) ≤ (460743571959853037408459099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772907 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_157_1 : expNegUpper (15314037801958232307731 / 208735537590964992000 : ℝ) ≤ (13743480797411269708975315623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_157 : rowCell 1 157 ≤ (1038658847168726014375664733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (460743571959853037408459099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13743480797411269708975315623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_157_1
  · norm_num [gridPoint]

theorem exp_1_158_0 : expNegUpper (46219982098240129753897 / 629994054503835904000 : ℝ) ≤ (6871738045094817328797373777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773881 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_158_1 : expNegUpper (92529060580177407737433 / 1259988109007671808000 : ℝ) ≤ (12805210550951367701336910397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774861 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_158 : rowCell 1 158 ≤ (1935954082207656042132603351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6871738045094817328797373777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12805210550951367701336910397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_158_1
  · norm_num [gridPoint]

theorem exp_1_159_0 : expNegUpper (3723480430596728857977 / 50703433231012352000 : ℝ) ≤ (1600650777198757739749983477 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774861 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_159_1 : expNegUpper (116471519017512647699 / 1584482288469136000 : ℝ) ≤ (11925624741621595460034908037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221981 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_159 : rowCell 1 159 ≤ (901697206325826986364860717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1600650777198757739749983477 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11925624741621595460034908037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_159_1
  · norm_num [gridPoint]

theorem sum_1_128_2 : blockSum (rowCell 1) 128 2 ≤ (25123584377955035536243409097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_128) (by simpa only [blockSum_one] using cell_1_129) (by norm_num)

theorem sum_1_130_2 : blockSum (rowCell 1) 130 2 ≤ (175505732770403871607285481 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_130) (by simpa only [blockSum_one] using cell_1_131) (by norm_num)

theorem sum_1_128_4 : blockSum (rowCell 1) 128 4 ≤ (9517663634513346220395190133 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_128_2 sum_1_130_2 (by norm_num)

theorem sum_1_132_2 : blockSum (rowCell 1) 132 2 ≤ (20040221925828107984593632901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_132) (by simpa only [blockSum_one] using cell_1_133) (by norm_num)

theorem sum_1_134_2 : blockSum (rowCell 1) 134 2 ≤ (2229539392270439308894996343 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_134) (by simpa only [blockSum_one] using cell_1_135) (by norm_num)

theorem sum_1_132_4 : blockSum (rowCell 1) 132 4 ≤ (7575307412798324491150720729 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_132_2 sum_1_134_2 (by norm_num)

theorem sum_1_128_8 : blockSum (rowCell 1) 128 8 ≤ (8546485523655835355772955431 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_128_4 sum_1_132_4 (by norm_num)

theorem sum_1_136_2 : blockSum (rowCell 1) 136 2 ≤ (15839022855538241342842974537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_136) (by simpa only [blockSum_one] using cell_1_137) (by norm_num)

theorem sum_1_138_2 : blockSum (rowCell 1) 138 2 ≤ (14034309727855416200434394327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_138) (by simpa only [blockSum_one] using cell_1_139) (by norm_num)

theorem sum_1_136_4 : blockSum (rowCell 1) 136 4 ≤ (933541643231051798227417777 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_136_2 sum_1_138_2 (by norm_num)

theorem sum_1_140_2 : blockSum (rowCell 1) 140 2 ≤ (193879318673790987190314157 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_140) (by simpa only [blockSum_one] using cell_1_141) (by norm_num)

theorem sum_1_142_2 : blockSum (rowCell 1) 142 2 ≤ (171051726823933921646522431 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_142) (by simpa only [blockSum_one] using cell_1_143) (by norm_num)

theorem sum_1_140_4 : blockSum (rowCell 1) 140 4 ≤ (91232761374431227209209147 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_140_2 sum_1_142_2 (by norm_num)

theorem sum_1_136_8 : blockSum (rowCell 1) 136 8 ≤ (1663403734226501615901090953 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_136_4 sum_1_140_4 (by norm_num)

theorem sum_1_128_16 : blockSum (rowCell 1) 128 16 ≤ (69346887365903202633282232403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_128_8 sum_1_136_8 (by norm_num)

theorem sum_1_144_2 : blockSum (rowCell 1) 144 2 ≤ (9638210093293848203213265949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_144) (by simpa only [blockSum_one] using cell_1_145) (by norm_num)

theorem sum_1_146_2 : blockSum (rowCell 1) 146 2 ≤ (8468281353466820969140283543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_146) (by simpa only [blockSum_one] using cell_1_147) (by norm_num)

theorem sum_1_144_4 : blockSum (rowCell 1) 144 4 ≤ (4526622861690167293088387373 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_144_2 sum_1_146_2 (by norm_num)

theorem sum_1_148_2 : blockSum (rowCell 1) 148 2 ≤ (928176703092180874624558337 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_148) (by simpa only [blockSum_one] using cell_1_149) (by norm_num)

theorem sum_1_150_2 : blockSum (rowCell 1) 150 2 ≤ (3249066834761334981910820039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_150) (by simpa only [blockSum_one] using cell_1_151) (by norm_num)

theorem sum_1_148_4 : blockSum (rowCell 1) 148 4 ≤ (6961773647130058480409053387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_148_2 sum_1_150_2 (by norm_num)

theorem sum_1_144_8 : blockSum (rowCell 1) 144 8 ≤ (16015019370510393066585828133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_144_4 sum_1_148_4 (by norm_num)

theorem sum_1_152_2 : blockSum (rowCell 1) 152 2 ≤ (88681905630477775810847713 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_152) (by simpa only [blockSum_one] using cell_1_153) (by norm_num)

theorem sum_1_154_2 : blockSum (rowCell 1) 154 2 ≤ (4947833303678024068079121353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_154) (by simpa only [blockSum_one] using cell_1_155) (by norm_num)

theorem sum_1_152_4 : blockSum (rowCell 1) 152 4 ≤ (2124695052805720343994674997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_152_2 sum_1_154_2 (by norm_num)

theorem sum_1_156_2 : blockSum (rowCell 1) 156 2 ≤ (2152652056765295682769806099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_156) (by simpa only [blockSum_one] using cell_1_157) (by norm_num)

theorem sum_1_158_2 : blockSum (rowCell 1) 158 2 ≤ (747869698971862002972464957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_158) (by simpa only [blockSum_one] using cell_1_159) (by norm_num)

theorem sum_1_156_4 : blockSum (rowCell 1) 156 4 ≤ (8044652608389901380401936983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_156_2 sum_1_158_2 (by norm_num)

theorem sum_1_152_8 : blockSum (rowCell 1) 152 8 ≤ (583378996013078221886728499 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_152_4 sum_1_156_4 (by norm_num)

theorem sum_1_144_16 : blockSum (rowCell 1) 144 16 ≤ (25349083306719644616773484117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_144_8 sum_1_152_8 (by norm_num)

theorem sum_1_128_32 : blockSum (rowCell 1) 128 32 ≤ (2367399266815571181251392913 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_128_16 sum_1_144_16 (by norm_num)

#print axioms sum_1_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
