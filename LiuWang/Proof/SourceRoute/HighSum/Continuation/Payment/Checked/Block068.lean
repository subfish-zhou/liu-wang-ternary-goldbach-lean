import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_128_0 : expNegUpper (622413755740601108563 / 8145908344958596000 : ℝ) ≤ (655839864197499819499246101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_128_1 : expNegUpper (79709373255728246726543 / 1042676268154700288000 : ℝ) ≤ (126181365727787966446298311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_128 : rowCell 4 128 ≤ (5864420306444689040184687 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (655839864197499819499246101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (126181365727787966446298311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_128_1
  · norm_num [gridPoint]

theorem exp_4_129_0 : expNegUpper (3209512745808217373983 / 41983553629987328000 : ℝ) ≤ (630906461126786118757725409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_129_1 : expNegUpper (1605584786162900407391 / 20991776814993664000 : ℝ) ≤ (606493437973399057087691053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_129 : rowCell 4 129 ≤ (90232312368857350845266693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (630906461126786118757725409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (606493437973399057087691053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_129_1
  · norm_num [gridPoint]

theorem exp_4_130_0 : expNegUpper (40404852156209159640631 / 528262125825210624000 : ℝ) ≤ (606493089313014889615245293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_130_1 : expNegUpper (80852136448145735400421 / 1056524251650421248000 : ℝ) ≤ (14565443964800684486241319 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181823 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_130 : rowCell 4 130 ≤ (4335551568550654847331299 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (606493089313014889615245293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14565443964800684486241319 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_130_1
  · norm_num [gridPoint]

theorem exp_4_131_0 : expNegUpper (81384627728774243420189 / 1063482500856914432000 : ℝ) ≤ (1820679462603000838068349 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181823 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_131_1 : expNegUpper (4071403733403451927411 / 53174125042845721600 : ℝ) ≤ (27964756620789021294961829 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181881 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_131 : rowCell 4 131 ≤ (83269289844988199577861753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1820679462603000838068349 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27964756620789021294961829 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_131_1
  · norm_num [gridPoint]

theorem exp_4_132_0 : expNegUpper (4098129944330592674771 / 53523179418458137600 : ℝ) ≤ (69911852402674342354070369 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181881 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_132_1 : expNegUpper (82007063960253576542011 / 1070463588369162752000 : ℝ) ≤ (536538645475237723877156427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9097 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_132 : rowCell 4 132 ≤ (79909160783556877561520953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (69911852402674342354070369 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (536538645475237723877156427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_132_1
  · norm_num [gridPoint]

theorem exp_4_133_0 : expNegUpper (82543627778269796236019 / 1077467514187166208000 : ℝ) ≤ (536538348923753534020930719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9097 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_133_1 : expNegUpper (41294557158518998055429 / 538733757093583104000 : ℝ) ≤ (514359214049011307104377583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91 / 50 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_133 : rowCell 4 133 ≤ (7663239445775324555826943 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (536538348923753534020930719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (514359214049011307104377583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_133_1
  · norm_num [gridPoint]

theorem exp_4_134_0 : expNegUpper (1662554487921734367421 / 21689885566218496000 : ℝ) ≤ (257179466717208772621452507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91 / 50 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_134_1 : expNegUpper (3326969429230437759353 / 43379771132436992000 : ℝ) ≤ (492765674725777004780522243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182061 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_134 : rowCell 4 134 ≤ (73440431265556530512499353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (257179466717208772621452507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (492765674725777004780522243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_134_1
  · norm_num [gridPoint]

theorem exp_4_135_0 : expNegUpper (83714898732401266629577 / 1091543880740438528000 : ℝ) ≤ (19710616374344975435512169 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182061 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_135_1 : expNegUpper (10470304774220133361247 / 136442985092554816000 : ℝ) ≤ (117941219414776121941482447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182123 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_135 : rowCell 4 135 ≤ (8791801887439066494701901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19710616374344975435512169 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (117941219414776121941482447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_135_1
  · norm_num [gridPoint]

theorem exp_4_136_0 : expNegUpper (10538145097444010967583 / 137327040184463424000 : ℝ) ≤ (471764626867183873333612737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182123 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_136_1 : expNegUpper (674829853587016092467 / 8788930571805659136 : ℝ) ≤ (22568089115903592024540503 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_136 : rowCell 4 136 ≤ (673152071291720990302573 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (471764626867183873333612737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22568089115903592024540503 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_136_1
  · norm_num [gridPoint]

theorem exp_4_137_0 : expNegUpper (679188164239022627467 / 8845692804133851136 : ℝ) ≤ (451361545446983842041440769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_137_1 : expNegUpper (42474063118473712359043 / 552855800258365696000 : ℝ) ≤ (107889888768156633921483969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911249 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_137 : rowCell 4 137 ≤ (12876679979863247366265809 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (451361545446983842041440769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107889888768156633921483969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_137_1
  · norm_num [gridPoint]

theorem exp_4_138_0 : expNegUpper (42747493987858567718387 / 556414858931755264000 : ℝ) ≤ (431559331486248260192593601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911249 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_138_1 : expNegUpper (85545631801810953098173 / 1112829717863510528000 : ℝ) ≤ (412359667990343042503985969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_138 : rowCell 4 138 ≤ (61539331650309130042633099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (431559331486248260192593601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (412359667990343042503985969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_138_1
  · norm_num [gridPoint]

theorem exp_4_139_0 : expNegUpper (3443782924376346219197 / 44798826940641792000 : ℝ) ≤ (25772466066949870746027197 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_139_1 : expNegUpper (861462583853062434277 / 11199706735160448000 : ℝ) ≤ (393761998260198404853918693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_139 : rowCell 4 139 ≤ (29391550386255222590074469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25772466066949870746027197 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (393761998260198404853918693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_139_1
  · norm_num [gridPoint]

theorem exp_4_140_0 : expNegUpper (21674321480822758822973 / 281783616868583552000 : ℝ) ≤ (19688089970486756661739561 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_140_1 : expNegUpper (86750015979771942435731 / 1127134467474334208000 : ℝ) ≤ (375764927698837943942783747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182447 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_140 : rowCell 4 140 ≤ (28057290156213017698206397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19688089970486756661739561 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (375764927698837943942783747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_140_1
  · norm_num [gridPoint]

theorem exp_4_141_0 : expNegUpper (87303136409702921601739 / 1134321099738378752000 : ℝ) ≤ (187882370168812154854637173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182447 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_141_1 : expNegUpper (8735691457754669685133 / 113432109973837875200 : ℝ) ≤ (358365441835158511321457461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_141 : rowCell 4 141 ≤ (26766716227062434584563367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (187882370168812154854637173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (358365441835158511321457461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_141_1
  · norm_num [gridPoint]

theorem exp_4_142_0 : expNegUpper (8791213456098296113853 / 114153057030817843200 : ℝ) ≤ (358365265402996203975148131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912573 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_142_1 : expNegUpper (87966964170969153403561 / 1141530570308178432000 : ℝ) ≤ (341559228109549901788439477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825831 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_142 : rowCell 4 142 ≤ (25519561452673501105211353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (358365265402996203975148131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341559228109549901788439477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_142_1
  · norm_num [gridPoint]

theorem exp_4_143_0 : expNegUpper (2855622269982896794559 / 37056867070443008000 : ℝ) ≤ (341559062065515933222491481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825831 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_143_1 : expNegUpper (178589062000762013753 / 2316054191902688000 : ℝ) ≤ (325340772764488842564060393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73061 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_143 : rowCell 4 143 ≤ (48630935123624303332771109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (341559062065515933222491481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (325340772764488842564060393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_143_1
  · norm_num [gridPoint]

theorem exp_4_144_0 : expNegUpper (222849034568755217023 / 2890045065912608000 : ℝ) ≤ (32534061658690931842412251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73061 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_144_1 : expNegUpper (3567862252564470393367 / 46240721054601728000 : ℝ) ≤ (154851728021543288223479063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456807 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_144 : rowCell 4 144 ≤ (46307984323588304165935999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32534061658690931842412251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154851728021543288223479063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_144_1
  · norm_num [gridPoint]

theorem exp_4_145_0 : expNegUpper (89758114927418466401207 / 1163296011852108288000 : ℝ) ≤ (154851654614724172314728613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456807 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_145_1 : expNegUpper (44908059424254601585343 / 581648005926054144000 : ℝ) ≤ (294639645351391964962801107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91397 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_145 : rowCell 4 145 ≤ (44069231212408131599183127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (154851654614724172314728613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (294639645351391964962801107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_145_1
  · norm_num [gridPoint]

theorem exp_4_146_0 : expNegUpper (45189901830778793068207 / 585298417822464256000 : ℝ) ≤ (29463950741819751996532059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91397 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_146_1 : expNegUpper (18087774469581787112017 / 234119367128985702400 : ℝ) ≤ (280140786078517712902452749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828661 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_146 : rowCell 4 146 ≤ (20956747702975206617905031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29463950741819751996532059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (280140786078517712902452749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_146_1
  · norm_num [gridPoint]

theorem exp_4_147_0 : expNegUpper (18200938004451618548777 / 235584099548700774400 : ℝ) ≤ (140070328280544279575442377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828661 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_147_1 : expNegUpper (22766206701162400932859 / 294480124435875968000 : ℝ) ≤ (133098744902893261277230861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182939 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_147 : rowCell 4 147 ≤ (7967893696750181489457017 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (140070328280544279575442377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133098744902893261277230861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_147_1
  · norm_num [gridPoint]

theorem exp_4_148_0 : expNegUpper (996008521759332966877 / 12883336936389504000 : ℝ) ≤ (66549342064505002454504509 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182939 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_148_1 : expNegUpper (3986695313524776278861 / 51533347745558016000 : ℝ) ≤ (252799619671912934595062991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114383 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_148 : rowCell 4 148 ≤ (7569145329241410721146323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66549342064505002454504509 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (252799619671912934595062991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_148_1
  · norm_num [gridPoint]

theorem exp_4_149_0 : expNegUpper (147622552948316565587 / 1908218138972672000 : ℝ) ≤ (126399752832998688387894473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114383 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_149_1 : expNegUpper (73861102847606667469 / 954109069486336000 : ℝ) ≤ (119968186347798958119460503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14647 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_149 : rowCell 4 149 ≤ (17965371471259122131201859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (126399752832998688387894473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119968186347798958119460503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_149_1
  · norm_num [gridPoint]

theorem exp_4_150_0 : expNegUpper (46449317393557200545261 / 600014256936880384000 : ℝ) ≤ (23993626582169059363033603 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14647 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_150_1 : expNegUpper (92961995842303690227841 / 1200028513873760768000 : ℝ) ≤ (227596358889694735105991231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_150 : rowCell 4 150 ≤ (34092899042796732306709271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23993626582169059363033603 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (227596358889694735105991231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_150_1
  · norm_num [gridPoint]

theorem exp_4_151_0 : expNegUpper (93536411577446922477689 / 1207443529195356672000 : ℝ) ≤ (28449532344445895240869693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_151_1 : expNegUpper (2340021351294864220441 / 30186088229883916800 : ℝ) ≤ (431535354064416023854681 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366479 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_151 : rowCell 4 151 ≤ (16165248266215312503356587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28449532344445895240869693 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (431535354064416023854681 / 2000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_151_1
  · norm_num [gridPoint]

theorem exp_4_152_0 : expNegUpper (2354435898900851609561 / 30372034570567692800 : ℝ) ≤ (215767583262862627650282771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366479 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_152_1 : expNegUpper (94242963180319616834711 / 1214881382822707712000 : ℝ) ≤ (102218993494368620672153347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_152 : rowCell 4 152 ≤ (7660441927797171342210691 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (215767583262862627650282771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (102218993494368620672153347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_152_1
  · norm_num [gridPoint]

theorem exp_4_153_0 : expNegUpper (94821717915214473533839 / 1222342074755813888000 : ℝ) ≤ (204437899225999457977277211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1833167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_153_1 : expNegUpper (47444166610108740504059 / 611171037377906944000 : ℝ) ≤ (9679728925425831972186533 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_153 : rowCell 4 153 ≤ (29024885883705128428246171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (204437899225999457977277211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9679728925425831972186533 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_153_1
  · norm_num [gridPoint]

theorem exp_4_154_0 : expNegUpper (1909385348946535933219 / 24596512099893504000 : ℝ) ≤ (24199312051325743656169957 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_154_1 : expNegUpper (3821478966553072322677 / 49193024199787008000 : ℝ) ≤ (183224436441899473006730751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1834737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_154 : rowCell 4 154 ≤ (27477975131864680063754421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24199312051325743656169957 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (183224436441899473006730751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_154_1
  · norm_num [gridPoint]

theorem exp_4_155_0 : expNegUpper (96120094544709680492837 / 1237331973539291648000 : ℝ) ≤ (91612179841491546868591151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1834737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_155_1 : expNegUpper (24047224000871561185049 / 309332993384822912000 : ℝ) ≤ (173314302350969449988658071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917767 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_155 : rowCell 4 155 ≤ (406236243175312353401981 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91612179841491546868591151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (173314302350969449988658071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_155_1
  · norm_num [gridPoint]

theorem exp_4_156_0 : expNegUpper (24193552299925442939641 / 311215295097415808000 : ℝ) ≤ (86657115310350879505925089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (917767 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_156_1 : expNegUpper (19368821746306887551399 / 248972236077932646400 : ℝ) ≤ (8192536625346648409206759 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1836339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_156 : rowCell 4 156 ≤ (6146593008228421072864117 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86657115310350879505925089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8192536625346648409206759 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_156_1
  · norm_num [gridPoint]

theorem exp_4_157_0 : expNegUpper (19486324280928343437439 / 250482645109157990400 : ℝ) ≤ (163850665509983754143904289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1836339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_157_1 : expNegUpper (48751311170155016923193 / 626206612772894976000 : ℝ) ≤ (154820152288067380808280523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_157 : rowCell 4 157 ≤ (5809440584911688549319969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (163850665509983754143904289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154820152288067380808280523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_157_1
  · norm_num [gridPoint]

theorem exp_4_158_0 : expNegUpper (49046170575934081753897 / 629994054503835904000 : ℝ) ≤ (38705022435910430705280123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1837153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_158_1 : expNegUpper (98164446822151679737433 / 1259988109007671808000 : ℝ) ≤ (146208907010298428119874013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_158 : rowCell 4 158 ≤ (21951304899036586924721681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38705022435910430705280123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146208907010298428119874013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_158_1
  · norm_num [gridPoint]

theorem exp_4_159_0 : expNegUpper (3950255137348790297977 / 50703433231012352000 : ℝ) ≤ (29241769730330159788311137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918987 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_159_1 : expNegUpper (123536990211747527699 / 1584482288469136000 : ℝ) ≤ (69001654619496351263999339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459701 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_159 : rowCell 4 159 ≤ (5181251475061582250545189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29241769730330159788311137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69001654619496351263999339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_159_1
  · norm_num [gridPoint]

theorem sum_4_128_2 : blockSum (rowCell 4) 128 2 ≤ (36812607454394475097644337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_128) (by simpa only [blockSum_one] using cell_4_129) (by norm_num)

theorem sum_4_130_2 : blockSum (rowCell 4) 130 2 ≤ (169980321216001296524487733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_130) (by simpa only [blockSum_one] using cell_4_131) (by norm_num)

theorem sum_4_128_4 : blockSum (rowCell 4) 128 4 ≤ (177021679243986836006354709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_128_2 sum_4_130_2 (by norm_num)

theorem sum_4_132_2 : blockSum (rowCell 4) 132 2 ≤ (156541555241310123119790383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_132) (by simpa only [blockSum_one] using cell_4_133) (by norm_num)

theorem sum_4_134_2 : blockSum (rowCell 4) 134 2 ≤ (143774846365069062470114561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_134) (by simpa only [blockSum_one] using cell_4_135) (by norm_num)

theorem sum_4_132_4 : blockSum (rowCell 4) 132 4 ≤ (18769775100398699099369059 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_132_2 sum_4_134_2 (by norm_num)

theorem sum_4_128_8 : blockSum (rowCell 4) 128 8 ≤ (327179880047176428801307181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_128_4 sum_4_132_4 (by norm_num)

theorem sum_4_136_2 : blockSum (rowCell 4) 136 2 ≤ (26339721405697667172317269 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_136) (by simpa only [blockSum_one] using cell_4_137) (by norm_num)

theorem sum_4_138_2 : blockSum (rowCell 4) 138 2 ≤ (120322432422819575222782037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_138) (by simpa only [blockSum_one] using cell_4_139) (by norm_num)

theorem sum_4_136_4 : blockSum (rowCell 4) 136 4 ≤ (126010519725653955542184191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_136_2 sum_4_138_2 (by norm_num)

theorem sum_4_140_2 : blockSum (rowCell 4) 140 2 ≤ (13706001595818863070692441 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_140) (by simpa only [blockSum_one] using cell_4_141) (by norm_num)

theorem sum_4_142_2 : blockSum (rowCell 4) 142 2 ≤ (19934011605794261108638763 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_142) (by simpa only [blockSum_one] using cell_4_143) (by norm_num)

theorem sum_4_140_4 : blockSum (rowCell 4) 140 4 ≤ (209318070795522210108733343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_140_2 sum_4_142_2 (by norm_num)

theorem sum_4_136_8 : blockSum (rowCell 4) 136 8 ≤ (18453564409873204847724069 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_136_4 sum_4_140_4 (by norm_num)

theorem sum_4_128_16 : blockSum (rowCell 4) 128 16 ≤ (1115698870341182978795716087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_128_8 sum_4_136_8 (by norm_num)

theorem sum_4_144_2 : blockSum (rowCell 4) 144 2 ≤ (45188607767998217882559563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_144) (by simpa only [blockSum_one] using cell_4_145) (by norm_num)

theorem sum_4_146_2 : blockSum (rowCell 4) 146 2 ≤ (81752963889701320683095147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_146) (by simpa only [blockSum_one] using cell_4_147) (by norm_num)

theorem sum_4_144_4 : blockSum (rowCell 4) 144 4 ≤ (172130179425697756448214273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_144_2 sum_4_146_2 (by norm_num)

theorem sum_4_148_2 : blockSum (rowCell 4) 148 2 ≤ (73776469588725297868135333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_148) (by simpa only [blockSum_one] using cell_4_149) (by norm_num)

theorem sum_4_150_2 : blockSum (rowCell 4) 150 2 ≤ (13284679115045471462684489 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_150) (by simpa only [blockSum_one] using cell_4_151) (by norm_num)

theorem sum_4_148_4 : blockSum (rowCell 4) 148 4 ≤ (70099932581976327590778889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_148_2 sum_4_150_2 (by norm_num)

theorem sum_4_144_8 : blockSum (rowCell 4) 144 8 ≤ (312330044589650411629772051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_144_4 sum_4_148_4 (by norm_num)

theorem sum_4_152_2 : blockSum (rowCell 4) 152 2 ≤ (11933330718978762759417787 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_152) (by simpa only [blockSum_one] using cell_4_153) (by norm_num)

theorem sum_4_154_2 : blockSum (rowCell 4) 154 2 ≤ (10695418939016934136296241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_154) (by simpa only [blockSum_one] using cell_4_155) (by norm_num)

theorem sum_4_152_4 : blockSum (rowCell 4) 152 4 ≤ (5657187414498924223928507 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_152_2 sum_4_154_2 (by norm_num)

theorem sum_4_156_2 : blockSum (rowCell 4) 156 2 ≤ (5978016796570054811092043 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_156) (by simpa only [blockSum_one] using cell_4_157) (by norm_num)

theorem sum_4_158_2 : blockSum (rowCell 4) 158 2 ≤ (42676310799282915926902437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_158) (by simpa only [blockSum_one] using cell_4_159) (by norm_num)

theorem sum_4_156_4 : blockSum (rowCell 4) 156 4 ≤ (90500445171843354415638781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_156_2 sum_4_158_2 (by norm_num)

theorem sum_4_152_8 : blockSum (rowCell 4) 152 8 ≤ (203644193461821838894208921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_152_4 sum_4_156_4 (by norm_num)

theorem sum_4_144_16 : blockSum (rowCell 4) 144 16 ≤ (128993559512868062630995243 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_144_8 sum_4_152_8 (by norm_num)

theorem sum_4_128_32 : blockSum (rowCell 4) 128 32 ≤ (1631673108392655229319697059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_128_16 sum_4_144_16 (by norm_num)

#print axioms sum_4_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
