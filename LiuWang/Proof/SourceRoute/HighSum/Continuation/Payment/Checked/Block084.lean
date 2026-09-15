import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_128_0 : expNegUpper (628153326670265108563 / 8145908344958596000 : ℝ) ≤ (324187184905077166957584711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114161 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_128_1 : expNegUpper (80441611089951862726543 / 1042676268154700288000 : ℝ) ≤ (312589404974305766902668477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228387 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_128 : rowCell 5 128 ≤ (46434321037972073295194303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (324187184905077166957584711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (312589404974305766902668477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_128_1
  · norm_num [gridPoint]

theorem exp_5_129_0 : expNegUpper (3238996438759032093983 / 41983553629987328000 : ℝ) ≤ (156294609464063342145398587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228387 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_129_1 : expNegUpper (1620278087742840247391 / 20991776814993664000 : ℝ) ≤ (301189246355790524187897581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_129 : rowCell 5 129 ≤ (8951455426018629272326683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156294609464063342145398587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (301189246355790524187897581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_129_1
  · norm_num [gridPoint]

theorem exp_5_130_0 : expNegUpper (40774611940481031640631 / 528262125825210624000 : ℝ) ≤ (75297267361080928772280039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (913813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_130_1 : expNegUpper (81589228771916103400421 / 1056524251650421248000 : ℝ) ≤ (28999787161217443316490087 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_130 : rowCell 5 130 ≤ (21554941443178600209119143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75297267361080928772280039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28999787161217443316490087 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_130_1
  · norm_num [gridPoint]

theorem exp_5_131_0 : expNegUpper (82126574542091363420189 / 1063482500856914432000 : ℝ) ≤ (144998851749801686909684101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1828167 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_131_1 : expNegUpper (4108379711830639127411 / 53174125042845721600 : ℝ) ≤ (279025144000492166187599131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914359 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_131 : rowCell 5 131 ≤ (41493657271171517644394783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144998851749801686909684101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (279025144000492166187599131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_131_1
  · norm_num [gridPoint]

theorem exp_5_132_0 : expNegUpper (4135348647235117474771 / 53523179418458137600 : ℝ) ≤ (17439061522195928908896553 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (914359 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_132_1 : expNegUpper (82749010773570696542011 / 1070463588369162752000 : ℝ) ≤ (268279849797757495742120919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_132 : rowCell 5 132 ≤ (3990996022561584500533139 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17439061522195928908896553 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (268279849797757495742120919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_132_1
  · norm_num [gridPoint]

theorem exp_5_133_0 : expNegUpper (83290429081133668236019 / 1077467514187166208000 : ℝ) ≤ (67069924573171422610574231 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1829279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_133_1 : expNegUpper (41666744187564246055429 / 538733757093583104000 : ℝ) ≤ (257769728182971713846097207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36597 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_133 : rowCell 5 133 ≤ (19179998400568268572079433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67069924573171422610574231 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (257769728182971713846097207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_133_1
  · norm_num [gridPoint]

theorem exp_5_134_0 : expNegUpper (1677539058874479327421 / 21689885566218496000 : ℝ) ≤ (32221198062071350691046467 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36597 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_134_1 : expNegUpper (3356841481344992639353 / 43379771132436992000 : ℝ) ≤ (123750751919624599560321847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830431 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_134 : rowCell 5 134 ≤ (36844821715941421452291633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32221198062071350691046467 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (123750751919624599560321847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_134_1
  · norm_num [gridPoint]

theorem exp_5_135_0 : expNegUpper (84466554524811890629577 / 1091543880740438528000 : ℝ) ≤ (30937670956965093579154981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1830431 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_135_1 : expNegUpper (10563958342674789361247 / 136442985092554816000 : ℝ) ≤ (118740460963999102761683247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915511 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_135 : rowCell 5 135 ≤ (3536534428272058400959761 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30937670956965093579154981 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118740460963999102761683247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_135_1
  · norm_num [gridPoint]

theorem exp_5_136_0 : expNegUpper (10632405477092010967583 / 137327040184463424000 : ℝ) ≤ (118740396468903530527369393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (915511 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_136_1 : expNegUpper (680843099926301084467 / 8788930571805659136 : ℝ) ≤ (56928196274320867210966981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831623 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_136 : rowCell 5 136 ≤ (16961166828837033670927179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (118740396468903530527369393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56928196274320867210966981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_136_1
  · norm_num [gridPoint]

theorem exp_5_137_0 : expNegUpper (685240246494681635467 / 8845692804133851136 : ℝ) ≤ (28464082874693959219404239 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1831623 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_137_1 : expNegUpper (42851104637065712359043 / 552855800258365696000 : ℝ) ≤ (21820099219824919056720443 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (916117 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_137 : rowCell 5 137 ≤ (8129106090606847250932811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28464082874693959219404239 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21820099219824919056720443 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_137_1
  · norm_num [gridPoint]

theorem exp_5_138_0 : expNegUpper (43126962751223943718387 / 556414858931755264000 : ℝ) ≤ (109100438346549472650627163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (916117 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_138_1 : expNegUpper (86302142083768329098173 / 1112829717863510528000 : ℝ) ≤ (208948578396580516048341969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (916427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_138 : rowCell 5 138 ≤ (31148122032227983455503619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (109100438346549472650627163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (208948578396580516048341969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_138_1
  · norm_num [gridPoint]

theorem exp_5_139_0 : expNegUpper (3474237515236511339197 / 44798826940641792000 : ℝ) ≤ (8357938767897142008253107 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (916427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_139_1 : expNegUpper (869051959120369954277 / 11199706735160448000 : ℝ) ≤ (99978878190109802939612313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458371 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_139 : rowCell 5 139 ≤ (29817809345809145960023707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8357938767897142008253107 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99978878190109802939612313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_139_1
  · norm_num [gridPoint]

theorem exp_5_140_0 : expNegUpper (21865269484892134822973 / 281783616868583552000 : ℝ) ≤ (49989413301506344962991401 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458371 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_140_1 : expNegUpper (87511380751276070435731 / 1127134467474334208000 : ℝ) ≤ (1493984049841622582617643 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458531 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_140 : rowCell 5 140 ≤ (7131438023613224492640699 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49989413301506344962991401 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1493984049841622582617643 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_140_1
  · norm_num [gridPoint]

theorem exp_5_141_0 : expNegUpper (88069355670753801601739 / 1134321099738378752000 : ℝ) ≤ (191229860957197889445192841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458531 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_141_1 : expNegUpper (8812070659382420085133 / 113432109973837875200 : ℝ) ≤ (3655317574672104038880683 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458693 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_141 : rowCell 5 141 ≤ (27272105350050739880004853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (191229860957197889445192841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3655317574672104038880683 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_141_1
  · norm_num [gridPoint]

theorem exp_5_142_0 : expNegUpper (8868078106680721713853 / 114153057030817843200 : ℝ) ≤ (182765786797357009230367443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (458693 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_142_1 : expNegUpper (88733183432020033403561 / 1141530570308178432000 : ℝ) ≤ (87282758373683235378243609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835431 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_142 : rowCell 5 142 ≤ (26056919694324264623142993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (182765786797357009230367443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87282758373683235378243609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_142_1
  · norm_num [gridPoint]

theorem exp_5_143_0 : expNegUpper (2880495616776368794559 / 37056867070443008000 : ℝ) ≤ (174565430040052117433525141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835431 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_143_1 : expNegUpper (180138752536698013753 / 2316054191902688000 : ℝ) ≤ (166628219612042795119403707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_143 : rowCell 5 143 ≤ (24880147473800370327382569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (174565430040052117433525141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (166628219612042795119403707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_143_1
  · norm_num [gridPoint]

theorem exp_5_144_0 : expNegUpper (224782787057182737023 / 2890045065912608000 : ℝ) ≤ (33325627576887574338737811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (918049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_144_1 : expNegUpper (3598705202588375673367 / 46240721054601728000 : ℝ) ≤ (39738181291224667530248923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73471 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_144 : rowCell 5 144 ≤ (23741649047614266517426099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33325627576887574338737811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39738181291224667530248923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_144_1
  · norm_num [gridPoint]

theorem exp_5_145_0 : expNegUpper (90534043167562850401207 / 1163296011852108288000 : ℝ) ≤ (3179052963519133356743477 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (73471 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_145_1 : expNegUpper (45294809921940105585343 / 581648005926054144000 : ℝ) ≤ (151537204292343318284557693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91873 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_145 : rowCell 5 145 ≤ (11320599498857630988132723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3179052963519133356743477 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (151537204292343318284557693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_145_1
  · norm_num [gridPoint]

theorem exp_5_146_0 : expNegUpper (45579079573237673068207 / 585298417822464256000 : ℝ) ≤ (75768565904609415596662341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (91873 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_146_1 : expNegUpper (18242960117610663912017 / 234119367128985702400 : ℝ) ≤ (72189651396084127343682609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367631 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_146 : rowCell 5 146 ≤ (21578492273554858486129879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75768565904609415596662341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (72189651396084127343682609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_146_1
  · norm_num [gridPoint]

theorem exp_5_147_0 : expNegUpper (18357094550389845748777 / 235584099548700774400 : ℝ) ≤ (144379234590211228719450487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (367631 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_147_1 : expNegUpper (22960795572391840932859 / 294480124435875968000 : ℝ) ≤ (137476182529218640669227983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_147 : rowCell 5 147 ≤ (20553150245825144313595713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (144379234590211228719450487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137476182529218640669227983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_147_1
  · norm_num [gridPoint]

theorem exp_5_148_0 : expNegUpper (23103998494080786238171 / 296316749536958592000 : ℝ) ≤ (68738059195971000180650909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1838859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_148_1 : expNegUpper (92474774940760990413803 / 1185266998147834368000 : ℝ) ≤ (65412280867650539408382113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_148 : rowCell 5 148 ≤ (782589065850834686144741 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68738059195971000180650909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65412280867650539408382113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_148_1
  · norm_num [gridPoint]

theorem exp_5_149_0 : expNegUpper (148879572499097186387 / 1908218138972672000 : ℝ) ≤ (32706125363580999552331391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_149_1 : expNegUpper (74487670827178277069 / 954109069486336000 : ℝ) ≤ (24884150864088972186969101 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_149 : rowCell 5 149 ≤ (9306356686502815176344921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32706125363580999552331391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24884150864088972186969101 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_149_1
  · norm_num [gridPoint]

theorem exp_5_150_0 : expNegUpper (996667013309847500963 / 12766260785891072000 : ℝ) ≤ (31105174423853468407985589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_150_1 : expNegUpper (1994630490671097409103 / 25532521571782144000 : ℝ) ≤ (59130354039240480654287323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_150 : rowCell 5 150 ≤ (17696546143107911347503267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31105174423853468407985589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59130354039240480654287323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_150_1
  · norm_num [gridPoint]

theorem exp_5_151_0 : expNegUpper (94326903286231562477689 / 1207443529195356672000 : ℝ) ≤ (118260654916971026914226431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1841023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_151_1 : expNegUpper (2359722962895145820441 / 30186088229883916800 : ℝ) ≤ (56170020842604135083688537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920881 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_151 : rowCell 5 151 ≤ (67262439906177071454611 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (118260654916971026914226431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56170020842604135083688537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_151_1
  · norm_num [gridPoint]

theorem exp_5_152_0 : expNegUpper (2374258872739802009561 / 30372034570567692800 : ℝ) ≤ (112339991802605831386673921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920881 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_152_1 : expNegUpper (95033454889104256834711 / 1214881382822707712000 : ℝ) ≤ (21330816080423161433225507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_152 : rowCell 5 152 ≤ (798462224882752415643371 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112339991802605831386673921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21330816080423161433225507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_152_1
  · norm_num [gridPoint]

theorem exp_5_153_0 : expNegUpper (95617064113545865533839 / 1222342074755813888000 : ℝ) ≤ (13331754202685723100518013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_153_1 : expNegUpper (47840626086887748504059 / 611171037377906944000 : ℝ) ≤ (1011978904126696964190321 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (368653 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_153 : rowCell 5 153 ≤ (15156749042533617127359171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13331754202685723100518013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1011978904126696964190321 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_153_1
  · norm_num [gridPoint]

theorem exp_5_154_0 : expNegUpper (1925340817808631293219 / 24596512099893504000 : ℝ) ≤ (101197846564608279281654909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (368653 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_154_1 : expNegUpper (3853292814486328002677 / 49193024199787008000 : ℝ) ≤ (2998947241609730373695809 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184403 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_154 : rowCell 5 154 ≤ (7188693781313257069207093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (101197846564608279281654909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2998947241609730373695809 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_154_1
  · norm_num [gridPoint]

theorem exp_5_155_0 : expNegUpper (96920295232587824492837 / 1237331973539291648000 : ℝ) ≤ (23991567663496591534688429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184403 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_155_1 : expNegUpper (24246667361647753185049 / 309332993384822912000 : ℝ) ≤ (22738497409878793847328133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1844803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_155 : rowCell 5 155 ≤ (851899582298343115688613 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23991567663496591534688429 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22738497409878793847328133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_155_1
  · norm_num [gridPoint]

theorem exp_5_156_0 : expNegUpper (24394209283088322939641 / 311215295097415808000 : ℝ) ≤ (90953951177695583425203283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1844803 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_156_1 : expNegUpper (19528861883882516351399 / 248972236077932646400 : ℝ) ≤ (21538851152373615324049253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115349 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_156 : rowCell 5 156 ≤ (6457486672844369057320157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90953951177695583425203283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21538851152373615324049253 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_156_1
  · norm_num [gridPoint]

theorem exp_5_157_0 : expNegUpper (19647335316413322637439 / 250482645109157990400 : ℝ) ≤ (86155368615570866945456427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (115349 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_157_1 : expNegUpper (49152625136480776923193 / 626206612772894976000 : ℝ) ≤ (81564900698409052599004709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_157 : rowCell 5 157 ≤ (1528789090569359689002009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86155368615570866945456427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81564900698409052599004709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_157_1
  · norm_num [gridPoint]

theorem exp_5_158_0 : expNegUpper (49449911787033217753897 / 629994054503835904000 : ℝ) ≤ (20391216757851573046471169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_158_1 : expNegUpper (98969501999576575737433 / 1259988109007671808000 : ℝ) ≤ (38588356196102251778484129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461793 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_158 : rowCell 5 158 ≤ (11575578590957462625893137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20391216757851573046471169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38588356196102251778484129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_158_1
  · norm_num [gridPoint]

theorem exp_5_159_0 : expNegUpper (3982651524027656217977 / 50703433231012352000 : ℝ) ≤ (77176680917788010583843769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (461793 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_159_1 : expNegUpper (124546343239495367699 / 1584482288469136000 : ℝ) ≤ (9123123737362899233100731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_159 : rowCell 5 159 ≤ (10949923946829246999399527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (77176680917788010583843769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9123123737362899233100731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_159_1
  · norm_num [gridPoint]

theorem sum_5_128_2 : blockSum (rowCell 5) 128 2 ≤ (45595799084032609828413859 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_128) (by simpa only [blockSum_one] using cell_5_129) (by norm_num)

theorem sum_5_130_2 : blockSum (rowCell 5) 130 2 ≤ (84603540157528718062633069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_130) (by simpa only [blockSum_one] using cell_5_131) (by norm_num)

theorem sum_5_128_4 : blockSum (rowCell 5) 128 4 ≤ (175795138325593937719460787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_128_2 sum_5_130_2 (by norm_num)

theorem sum_5_132_2 : blockSum (rowCell 5) 132 2 ≤ (4891872314172023884343141 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_132) (by simpa only [blockSum_one] using cell_5_133) (by norm_num)

theorem sum_5_134_2 : blockSum (rowCell 5) 134 2 ≤ (72210165998662005461889243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_134) (by simpa only [blockSum_one] using cell_5_135) (by norm_num)

theorem sum_5_132_4 : blockSum (rowCell 5) 132 4 ≤ (150480123025414387611379499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_132_2 sum_5_134_2 (by norm_num)

theorem sum_5_128_8 : blockSum (rowCell 5) 128 8 ≤ (163137630675504162665420143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_128_4 sum_5_132_4 (by norm_num)

theorem sum_5_136_2 : blockSum (rowCell 5) 136 2 ≤ (33219379010050728172792801 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_136) (by simpa only [blockSum_one] using cell_5_137) (by norm_num)

theorem sum_5_138_2 : blockSum (rowCell 5) 138 2 ≤ (30482965689018564707763663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_138) (by simpa only [blockSum_one] using cell_5_139) (by norm_num)

theorem sum_5_136_4 : blockSum (rowCell 5) 136 4 ≤ (3981396543691830805034779 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_136_2 sum_5_138_2 (by norm_num)

theorem sum_5_140_2 : blockSum (rowCell 5) 140 2 ≤ (55797857444503637850567649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_140) (by simpa only [blockSum_one] using cell_5_141) (by norm_num)

theorem sum_5_142_2 : blockSum (rowCell 5) 142 2 ≤ (25468533584062317475262781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_142) (by simpa only [blockSum_one] using cell_5_143) (by norm_num)

theorem sum_5_140_4 : blockSum (rowCell 5) 140 4 ≤ (106734924612628272801093211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_140_2 sum_5_142_2 (by norm_num)

theorem sum_5_136_8 : blockSum (rowCell 5) 136 8 ≤ (234139614010766858562206139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_136_4 sum_5_140_4 (by norm_num)

theorem sum_5_128_16 : blockSum (rowCell 5) 128 16 ≤ (22416595014471007355721857 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_128_8 sum_5_136_8 (by norm_num)

theorem sum_5_144_2 : blockSum (rowCell 5) 144 2 ≤ (9276569609065905698738309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_144) (by simpa only [blockSum_one] using cell_5_145) (by norm_num)

theorem sum_5_146_2 : blockSum (rowCell 5) 146 2 ≤ (5266455314922500349965699 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_146) (by simpa only [blockSum_one] using cell_5_147) (by norm_num)

theorem sum_5_144_4 : blockSum (rowCell 5) 144 4 ≤ (88514490564709531293417137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_144_2 sum_5_146_2 (by norm_num)

theorem sum_5_148_2 : blockSum (rowCell 5) 148 2 ≤ (38177440019276497506308367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_148) (by simpa only [blockSum_one] using cell_5_149) (by norm_num)

theorem sum_5_150_2 : blockSum (rowCell 5) 150 2 ≤ (34512156119652179211156017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_150) (by simpa only [blockSum_one] using cell_5_151) (by norm_num)

theorem sum_5_148_4 : blockSum (rowCell 5) 148 4 ≤ (1135774939670760573710381 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_148_2 sum_5_150_2 (by norm_num)

theorem sum_5_144_8 : blockSum (rowCell 5) 144 8 ≤ (161204086703638208010881521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_144_4 sum_5_148_4 (by norm_num)

theorem sum_5_152_2 : blockSum (rowCell 5) 152 2 ≤ (31125993540188665440226591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_152) (by simpa only [blockSum_one] using cell_5_153) (by norm_num)

theorem sum_5_154_2 : blockSum (rowCell 5) 154 2 ≤ (14003890439700001994715997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_154) (by simpa only [blockSum_one] using cell_5_155) (by norm_num)

theorem sum_5_152_4 : blockSum (rowCell 5) 152 4 ≤ (11826754883917733885931717 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_152_2 sum_5_154_2 (by norm_num)

theorem sum_5_156_2 : blockSum (rowCell 5) 156 2 ≤ (12572643035121807813328193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_156) (by simpa only [blockSum_one] using cell_5_157) (by norm_num)

theorem sum_5_158_2 : blockSum (rowCell 5) 158 2 ≤ (2815687817223338703161583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_158) (by simpa only [blockSum_one] using cell_5_159) (by norm_num)

theorem sum_5_156_4 : blockSum (rowCell 5) 156 4 ≤ (953415772160606505038981 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_156_2 sum_5_158_2 (by norm_num)

theorem sum_5_152_8 : blockSum (rowCell 5) 152 8 ≤ (21360912605523798936321527 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_152_4 sum_5_156_4 (by norm_num)

theorem sum_5_144_16 : blockSum (rowCell 5) 144 16 ≤ (67002162432814300673122289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_144_8 sum_5_152_8 (by norm_num)

theorem sum_5_128_32 : blockSum (rowCell 5) 128 32 ≤ (828423525093032386585535581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_128_16 sum_5_144_16 (by norm_num)

#print axioms sum_5_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
