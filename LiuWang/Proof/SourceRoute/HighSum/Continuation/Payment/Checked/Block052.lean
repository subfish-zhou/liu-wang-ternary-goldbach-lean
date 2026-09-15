import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_128_0 : expNegUpper (616674184810937108563 / 8145908344958596000 : ℝ) ≤ (331695658787790279341138023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_128_1 : expNegUpper (78977135421504630726543 / 1042676268154700288000 : ℝ) ≤ (318343664315784291652699129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_128 : rowCell 3 128 ≤ (18960580584166803433859693 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (331695658787790279341138023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (318343664315784291652699129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_128_1
  · norm_num [gridPoint]

theorem exp_3_129_0 : expNegUpper (3180029052857402653983 / 41983553629987328000 : ℝ) ≤ (1273373931629569382553440147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807157 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_129_1 : expNegUpper (1590891484582960567391 / 20991776814993664000 : ℝ) ≤ (1221272986188477305150348473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807747 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_129 : rowCell 3 129 ≤ (181911894531632191618681251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1273373931629569382553440147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1221272986188477305150348473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_129_1
  · norm_num [gridPoint]

theorem exp_3_130_0 : expNegUpper (4448343596881920848959 / 58695791758356736000 : ℝ) ≤ (1221272299366895053284110859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807747 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_130_1 : expNegUpper (8901671569375040822269 / 117391583516713472000 : ℝ) ≤ (1170503254867846001404801609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (904173 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_130 : rowCell 3 130 ≤ (8720521113782341274154091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1221272299366895053284110859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1170503254867846001404801609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_130_1
  · norm_num [gridPoint]

theorem exp_3_131_0 : expNegUpper (80642680915457123420189 / 1063482500856914432000 : ℝ) ≤ (58525130259903228738402843 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (904173 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_131_1 : expNegUpper (4034427754976264727411 / 53174125042845721600 : ℝ) ≤ (1121085507417330103287695433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452239 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_131 : rowCell 3 131 ≤ (167104664020609507817481523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58525130259903228738402843 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1121085507417330103287695433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_131_1
  · norm_num [gridPoint]

theorem exp_3_132_0 : expNegUpper (4060911241426067874771 / 53523179418458137600 : ℝ) ≤ (224216978655758146977966349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452239 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_132_1 : expNegUpper (81265117146936456542011 / 1070463588369162752000 : ℝ) ≤ (536517592181105209563736061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72383 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_132 : rowCell 3 132 ≤ (159997207341339059737916111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (224216978655758146977966349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (536517592181105209563736061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_132_1
  · norm_num [gridPoint]

theorem exp_3_133_0 : expNegUpper (9088536275045102692891 / 119718612687462912000 : ℝ) ≤ (1073034604175548240952754239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72383 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_133_1 : expNegUpper (4546930014385972228381 / 59859306343731456000 : ℝ) ≤ (64147709212706982920490933 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452551 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_133 : rowCell 3 133 ≤ (76544992403488795237636117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1073034604175548240952754239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64147709212706982920490933 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_133_1
  · norm_num [gridPoint]

theorem exp_3_134_0 : expNegUpper (1647569916968989407421 / 21689885566218496000 : ℝ) ≤ (256590699907916382704907699 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452551 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_134_1 : expNegUpper (3297097377115882879353 / 43379771132436992000 : ℝ) ≤ (490538454153513275479141209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (905421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_134 : rowCell 3 134 ≤ (73192153531001013885956327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (256590699907916382704907699 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (490538454153513275479141209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_134_1
  · norm_num [gridPoint]

theorem exp_3_135_0 : expNegUpper (82963242939990642629577 / 1091543880740438528000 : ℝ) ≤ (196215278291420927493078529 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (905421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_135_1 : expNegUpper (10376651205765477361247 / 136442985092554816000 : ℝ) ≤ (468589430228396166355975417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181149 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_135 : rowCell 3 135 ≤ (139880896402014258457141031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (196215278291420927493078529 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (468589430228396166355975417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_135_1
  · norm_num [gridPoint]

theorem exp_3_136_0 : expNegUpper (1160431635310667885287 / 15258560020495936000 : ℝ) ≤ (937178373079708831200957933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181149 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_136_1 : expNegUpper (74312956360859011163 / 976547841311739904 : ℝ) ≤ (178933702339383371270807507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_136 : rowCell 3 136 ≤ (133579920637847086636151433 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (937178373079708831200957933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (178933702339383371270807507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_136_1
  · norm_num [gridPoint]

theorem exp_3_137_0 : expNegUpper (673136081983363619467 / 8845692804133851136 : ℝ) ≤ (894668052388812911737541069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_137_1 : expNegUpper (42097021599881712359043 / 552855800258365696000 : ℝ) ≤ (853541717194711109744704477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_137 : rowCell 3 137 ≤ (31870256763811357960962099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (894668052388812911737541069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (853541717194711109744704477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_137_1
  · norm_num [gridPoint]

theorem exp_3_138_0 : expNegUpper (42368025224493191718387 / 556414858931755264000 : ℝ) ≤ (426770642298587620813040317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1812813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_138_1 : expNegUpper (84789121519853577098173 / 1112829717863510528000 : ℝ) ≤ (813791111143011682106572777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_138 : rowCell 3 138 ≤ (60791688145661864151387189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (426770642298587620813040317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (813791111143011682106572777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_138_1
  · norm_num [gridPoint]

theorem exp_3_139_0 : expNegUpper (379258703724020122133 / 4977647437849088000 : ℝ) ≤ (40689535197165673240664407 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1813489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_139_1 : expNegUpper (94874800953972768253 / 1244411859462272000 : ℝ) ≤ (193851584055383928264185503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_139 : rowCell 3 139 ≤ (57942837981518287578482921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40689535197165673240664407 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (193851584055383928264185503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_139_1
  · norm_num [gridPoint]

theorem exp_3_140_0 : expNegUpper (21483373476753382822973 / 281783616868583552000 : ℝ) ≤ (387702976576343345763820659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_140_1 : expNegUpper (85988651208267814435731 / 1127134467474334208000 : ℝ) ≤ (738374269831360582143995663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_140 : rowCell 3 140 ≤ (110386213896915814426108209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (387702976576343345763820659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (738374269831360582143995663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_140_1
  · norm_num [gridPoint]

theorem exp_3_141_0 : expNegUpper (86536917148652041601739 / 1134321099738378752000 : ℝ) ≤ (92296738709002005535194183 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1814867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_141_1 : expNegUpper (8659312256126919285133 / 113432109973837875200 : ℝ) ≤ (175669811552869879529529627 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181557 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_141 : rowCell 3 141 ≤ (13135361352902404436028553 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (92296738709002005535194183 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (175669811552869879529529627 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_141_1
  · norm_num [gridPoint]

theorem exp_3_142_0 : expNegUpper (968260978390652279317 / 12683673003424204800 : ℝ) ≤ (28107156311427775801373143 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181557 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_142_1 : expNegUpper (9688971656657585933729 / 126836730034242048000 : ℝ) ≤ (334151636819622739126510653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_142 : rowCell 3 142 ≤ (1249665655141377994119137 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28107156311427775801373143 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (334151636819622739126510653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_142_1
  · norm_num [gridPoint]

theorem exp_3_143_0 : expNegUpper (2830748923189424794559 / 37056867070443008000 : ℝ) ≤ (167075738954024311875259867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_143_1 : expNegUpper (177039371464826013753 / 2316054191902688000 : ℝ) ≤ (317613123003520543826513841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_143 : rowCell 3 143 ≤ (95054520536460510375282567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167075738954024311875259867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (317613123003520543826513841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_143_1
  · norm_num [gridPoint]

theorem exp_3_144_0 : expNegUpper (220915282080327697023 / 2890045065912608000 : ℝ) ≤ (158806486925033029536366283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_144_1 : expNegUpper (3537019302540565113367 / 46240721054601728000 : ℝ) ≤ (301713074077616127438170857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_144 : rowCell 3 144 ≤ (45161811840632770067339521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (158806486925033029536366283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (301713074077616127438170857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_144_1
  · norm_num [gridPoint]

theorem exp_3_145_0 : expNegUpper (9886909631919342489023 / 129255112428012032000 : ℝ) ≤ (942852919253255566326869 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_145_1 : expNegUpper (4946812102952121953927 / 64627556214006016000 : ℝ) ≤ (572879254425973245046747727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818469 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_145 : rowCell 3 145 ≤ (85777226387422021359892213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (942852919253255566326869 / 1562500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (572879254425973245046747727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_145_1
  · norm_num [gridPoint]

theorem exp_3_146_0 : expNegUpper (44800724088319913068207 / 585298417822464256000 : ℝ) ≤ (572878992067321130828152251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818469 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_146_1 : expNegUpper (17932588821552910312017 / 234119367128985702400 : ℝ) ≤ (543560319983390649876186031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113701 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_146 : rowCell 3 146 ≤ (3256470307427292944413033 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (572878992067321130828152251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (543560319983390649876186031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_146_1
  · norm_num [gridPoint]

theorem exp_3_147_0 : expNegUpper (18044781458513391348777 / 235584099548700774400 : ℝ) ≤ (543560074142397175632960949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113701 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_147_1 : expNegUpper (22571617829932960932859 / 294480124435875968000 : ℝ) ≤ (128860691130700553667229069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_147 : rowCell 3 147 ≤ (1206616225677018793842033 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (543560074142397175632960949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (128860691130700553667229069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_147_1
  · norm_num [gridPoint]

theorem exp_3_148_0 : expNegUpper (2523599278538725582019 / 32924083281884288000 : ℝ) ≤ (32215158392761870973524943 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_148_1 : expNegUpper (10101467720153190934867 / 131696333127537152000 : ℝ) ≤ (61062356008087521121469809 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_148 : rowCell 3 148 ≤ (14641661515893354100920991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32215158392761870973524943 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61062356008087521121469809 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_148_1
  · norm_num [gridPoint]

theorem exp_3_149_0 : expNegUpper (146365533397535944787 / 1908218138972672000 : ℝ) ≤ (48849863255382099980148449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910367 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_149_1 : expNegUpper (73234534868035057869 / 954109069486336000 : ℝ) ≤ (231349919299038646864232899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910753 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_149 : rowCell 3 149 ≤ (69362247108772849097827069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (48849863255382099980148449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (231349919299038646864232899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_149_1
  · norm_num [gridPoint]

theorem exp_3_150_0 : expNegUpper (46055285161551568545261 / 600014256936880384000 : ℝ) ≤ (462699636979924833867997843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910753 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_150_1 : expNegUpper (92176358623065802227841 / 1200028513873760768000 : ℝ) ≤ (109504042850544234596944217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911143 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_150 : rowCell 3 150 ≤ (65681005984081954527452103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (462699636979924833867997843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (109504042850544234596944217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_150_1
  · norm_num [gridPoint]

theorem exp_3_151_0 : expNegUpper (10305102207629142497521 / 134160392132817408000 : ℝ) ≤ (109503995720087757143544429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911143 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_151_1 : expNegUpper (257813304410509180049 / 3354009803320435200 : ℝ) ≤ (414417599935831054670819341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72923 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_151 : rowCell 3 151 ≤ (62160222717253058923815601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109503995720087757143544429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (414417599935831054670819341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_151_1
  · norm_num [gridPoint]

theorem exp_3_152_0 : expNegUpper (2334612925061901209561 / 30372034570567692800 : ℝ) ≤ (207208711875731393801664657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72923 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_152_1 : expNegUpper (93452471471534976834711 / 1214881382822707712000 : ℝ) ≤ (391873338239180665867838011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28498 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_152 : rowCell 3 152 ≤ (235181787064856786383381 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (207208711875731393801664657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (391873338239180665867838011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_152_1
  · norm_num [gridPoint]

theorem exp_3_153_0 : expNegUpper (94026371716883081533839 / 1222342074755813888000 : ℝ) ≤ (391873173669825527340552169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28498 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_153_1 : expNegUpper (47047707133329732504059 / 611171037377906944000 : ℝ) ≤ (92588048710939242118757111 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_153 : rowCell 3 153 ≤ (55582158683864959516645723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (391873173669825527340552169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92588048710939242118757111 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_153_1
  · norm_num [gridPoint]

theorem exp_3_154_0 : expNegUpper (210381097787160063691 / 2732945788877056000 : ℝ) ≤ (370352041202263248330431929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_154_1 : expNegUpper (421073902068868515853 / 5465891577754112000 : ℝ) ≤ (87455674558419719001510683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182549 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_154 : rowCell 3 154 ≤ (26257894515830680842934033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (370352041202263248330431929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87455674558419719001510683 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_154_1
  · norm_num [gridPoint]

theorem exp_3_155_0 : expNegUpper (95319893856831536492837 / 1237331973539291648000 : ℝ) ≤ (349822554867037961684479041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182549 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_155_1 : expNegUpper (23847780640095369185049 / 309332993384822912000 : ℝ) ≤ (330253213943165401812661109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_155 : rowCell 3 155 ≤ (12397934016803392420823963 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (349822554867037961684479041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (330253213943165401812661109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_155_1
  · norm_num [gridPoint]

theorem exp_3_156_0 : expNegUpper (23992895316762562939641 / 311215295097415808000 : ℝ) ≤ (165126540115675026921921309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_156_1 : expNegUpper (19208781608731258751399 / 248972236077932646400 : ℝ) ≤ (311612053413767051129639551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91357 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_156 : rowCell 3 156 ≤ (1170134555527698714489133 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (165126540115675026921921309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (311612053413767051129639551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_156_1
  · norm_num [gridPoint]

theorem exp_3_157_0 : expNegUpper (2147257027271484915271 / 27831405012128665600 : ℝ) ≤ (155805964384281630767478647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91357 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_157_1 : expNegUpper (5372221911536584102577 / 69578512530321664000 : ℝ) ≤ (58773514953762221163983137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_157 : rowCell 3 157 ≤ (44152109383436798227300509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155805964384281630767478647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58773514953762221163983137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_157_1
  · norm_num [gridPoint]

theorem exp_3_158_0 : expNegUpper (48642429364834945753897 / 629994054503835904000 : ℝ) ≤ (293867458632648658715055637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1827977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_158_1 : expNegUpper (97359391644726783737433 / 1259988109007671808000 : ℝ) ≤ (5539765513853464936264949 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_158 : rowCell 3 158 ≤ (260170706407508007859521 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (293867458632648658715055637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5539765513853464936264949 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_158_1
  · norm_num [gridPoint]

theorem exp_3_159_0 : expNegUpper (3917858750669924377977 / 50703433231012352000 : ℝ) ≤ (27698816753745963687773247 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_159_1 : expNegUpper (122527637183999687699 / 1584482288469136000 : ℝ) ≤ (65235719657197802663415937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73187 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_159 : rowCell 3 159 ≤ (19613207591933650896492621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27698816753745963687773247 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65235719657197802663415937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_159_1
  · norm_num [gridPoint]

theorem sum_3_128_2 : blockSum (rowCell 3) 128 2 ≤ (371517700373300225957278181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_128) (by simpa only [blockSum_one] using cell_3_129) (by norm_num)

theorem sum_3_130_2 : blockSum (rowCell 3) 130 2 ≤ (341515086296256333300563343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_130) (by simpa only [blockSum_one] using cell_3_131) (by norm_num)

theorem sum_3_128_4 : blockSum (rowCell 3) 128 4 ≤ (178258196667389139814460381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_128_2 sum_3_130_2 (by norm_num)

theorem sum_3_132_2 : blockSum (rowCell 3) 132 2 ≤ (62617438429663330042637669 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_132) (by simpa only [blockSum_one] using cell_3_133) (by norm_num)

theorem sum_3_134_2 : blockSum (rowCell 3) 134 2 ≤ (57253040692803257245810737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_134) (by simpa only [blockSum_one] using cell_3_135) (by norm_num)

theorem sum_3_132_4 : blockSum (rowCell 3) 132 4 ≤ (59935239561233293644224203 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_132_2 sum_3_134_2 (by norm_num)

theorem sum_3_128_8 : blockSum (rowCell 3) 128 8 ≤ (656192591140944747850041777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_128_4 sum_3_132_4 (by norm_num)

theorem sum_3_136_2 : blockSum (rowCell 3) 136 2 ≤ (261060947693092518479999829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_136) (by simpa only [blockSum_one] using cell_3_137) (by norm_num)

theorem sum_3_138_2 : blockSum (rowCell 3) 138 2 ≤ (11873452612718015172987011 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_138) (by simpa only [blockSum_one] using cell_3_139) (by norm_num)

theorem sum_3_136_4 : blockSum (rowCell 3) 136 4 ≤ (498529999947452821939740049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_136_2 sum_3_138_2 (by norm_num)

theorem sum_3_140_2 : blockSum (rowCell 3) 140 2 ≤ (215469104720135049914336633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_140) (by simpa only [blockSum_one] using cell_3_141) (by norm_num)

theorem sum_3_142_2 : blockSum (rowCell 3) 142 2 ≤ (195027772947770749904813527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_142) (by simpa only [blockSum_one] using cell_3_143) (by norm_num)

theorem sum_3_140_4 : blockSum (rowCell 3) 140 4 ≤ (5131210970848822497739377 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_140_2 sum_3_142_2 (by norm_num)

theorem sum_3_136_8 : blockSum (rowCell 3) 136 8 ≤ (909026877615358621758890209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_136_4 sum_3_140_4 (by norm_num)

theorem sum_3_128_16 : blockSum (rowCell 3) 128 16 ≤ (2221412059897248117458973763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_128_8 sum_3_136_8 (by norm_num)

theorem sum_3_144_2 : blockSum (rowCell 3) 144 2 ≤ (35220170013737512298914251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_144) (by simpa only [blockSum_one] using cell_3_145) (by norm_num)

theorem sum_3_146_2 : blockSum (rowCell 3) 146 2 ≤ (158635196129011526416215937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_146) (by simpa only [blockSum_one] using cell_3_147) (by norm_num)

theorem sum_3_144_4 : blockSum (rowCell 3) 144 4 ≤ (41842005774712385988848399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_144_2 sum_3_146_2 (by norm_num)

theorem sum_3_148_2 : blockSum (rowCell 3) 148 2 ≤ (17821319336029952450304003 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_148) (by simpa only [blockSum_one] using cell_3_149) (by norm_num)

theorem sum_3_150_2 : blockSum (rowCell 3) 150 2 ≤ (15980153587666876681408463 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_150) (by simpa only [blockSum_one] using cell_3_151) (by norm_num)

theorem sum_3_148_4 : blockSum (rowCell 3) 148 4 ≤ (16900736461848414565856233 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_148_2 sum_3_150_2 (by norm_num)

theorem sum_3_144_8 : blockSum (rowCell 3) 144 8 ≤ (15128695739681843024112173 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_144_4 sum_3_148_4 (by norm_num)

theorem sum_3_152_2 : blockSum (rowCell 3) 152 2 ≤ (114377605450079156112490973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_152) (by simpa only [blockSum_one] using cell_3_153) (by norm_num)

theorem sum_3_154_2 : blockSum (rowCell 3) 154 2 ≤ (51053762549437465684581959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_154) (by simpa only [blockSum_one] using cell_3_155) (by norm_num)

theorem sum_3_152_4 : blockSum (rowCell 3) 152 4 ≤ (216485130548954087481654891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_152_2 sum_3_154_2 (by norm_num)

theorem sum_3_156_2 : blockSum (rowCell 3) 156 2 ≤ (90957491604544746806865829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_156) (by simpa only [blockSum_one] using cell_3_157) (by norm_num)

theorem sum_3_158_2 : blockSum (rowCell 3) 158 2 ≤ (40426864104534291525254301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_158) (by simpa only [blockSum_one] using cell_3_159) (by norm_num)

theorem sum_3_156_4 : blockSum (rowCell 3) 156 4 ≤ (171811219813613329857374431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_156_2 sum_3_158_2 (by norm_num)

theorem sum_3_152_8 : blockSum (rowCell 3) 152 8 ≤ (194148175181283708669514661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_152_4 sum_3_156_4 (by norm_num)

theorem sum_3_144_16 : blockSum (rowCell 3) 144 16 ≤ (496722089974920569151758121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_144_8 sum_3_152_8 (by norm_num)

theorem sum_3_128_32 : blockSum (rowCell 3) 128 32 ≤ (642971247969417851152498001 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_128_16 sum_3_144_16 (by norm_num)

#print axioms sum_3_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
