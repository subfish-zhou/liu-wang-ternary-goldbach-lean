import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_256_0 : expNegUpper (229586087931113723323 / 2751452225898774000 : ℝ) ≤ (578264911279677856823517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (959581 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_256_1 : expNegUpper (11768556785623578569473 / 140874353966017228800 : ℝ) ≤ (524493946566594846102597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (960313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_256 : rowCell 2 256 ≤ (20103541668515387939501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (578264911279677856823517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (524493946566594846102597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_256_1
  · norm_num [gridPoint]

theorem exp_2_257_0 : expNegUpper (5067143858911233685837 / 60655748149197107200 : ℝ) ≤ (52449387851410743541123 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (960313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_257_1 : expNegUpper (12682693271210147118849 / 151639370372992768000 : ℝ) ≤ (475616585653236160760269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961047 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_257 : rowCell 2 257 ≤ (18232238395956961345147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52449387851410743541123 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (475616585653236160760269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_257_1
  · norm_num [gridPoint]

theorem exp_2_258_0 : expNegUpper (89191130684421096147447 / 1066404949629647104000 : ℝ) ≤ (237808262256186646434337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (961047 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_258_1 : expNegUpper (178591369916461163493733 / 2132809899259294208000 : ℝ) ≤ (431198362093849982538879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923567 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_258 : rowCell 2 258 ≤ (66125756247825486521443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (237808262256186646434337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (431198362093849982538879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_258_1
  · norm_num [gridPoint]

theorem exp_2_259_0 : expNegUpper (2392250725923747014839 / 28569219354699264000 : ℝ) ≤ (86239661434731601812631 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923567 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_259_1 : expNegUpper (598764513784165455869 / 7142304838674816000 : ℝ) ≤ (24427639339094913150807 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481261 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_259 : rowCell 2 259 ≤ (59943934480856559914939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86239661434731601812631 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24427639339094913150807 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_259_1
  · norm_num [gridPoint]

theorem exp_2_260_0 : expNegUpper (45114918570137081796863 / 538148960562837632000 : ℝ) ≤ (97710545025726387409127 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (481261 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_260_1 : expNegUpper (180671668445646126193851 / 2152595842251350528000 : ℝ) ≤ (177092754944667993537961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963263 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_260 : rowCell 2 260 ≤ (54328088515049480261577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (97710545025726387409127 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (177092754944667993537961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_260_1
  · norm_num [gridPoint]

theorem exp_2_261_0 : expNegUpper (181504880869982742247539 / 2162523071206011392000 : ℝ) ≤ (35418546560253887526199 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (963263 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_261_1 : expNegUpper (726873291359957114089 / 8650092284824045568 : ℝ) ≤ (160448508775934732124603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_261 : rowCell 2 261 ≤ (49227621191037915155899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35418546560253887526199 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (160448508775934732124603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_261_1
  · norm_num [gridPoint]

theorem exp_2_262_0 : expNegUpper (243405912273230557363 / 2896630851288569856 : ℝ) ≤ (160448488897268130845921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_262_1 : expNegUpper (60923109103539246824987 / 724157712822142464000 : ℝ) ≤ (145337206291688592645913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_262 : rowCell 2 262 ≤ (22298167622514245605331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (160448488897268130845921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (145337206291688592645913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_262_1
  · norm_num [gridPoint]

theorem exp_2_263_0 : expNegUpper (183608344277707501240649 / 2182446044032598528000 : ℝ) ≤ (58134875379841390856469 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929503 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_263_1 : expNegUpper (22978086481233769847631 / 272805755504074816000 : ℝ) ≤ (10529670762354428560667 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965499 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_263 : rowCell 2 263 ≤ (20196031511149839286893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58134875379841390856469 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10529670762354428560667 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_263_1
  · norm_num [gridPoint]

theorem exp_2_264_0 : expNegUpper (131904729343339384737 / 1566029848503232000 : ℝ) ≤ (16452608564796923639499 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (965499 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_264_1 : expNegUpper (1056482436857629600969 / 12528238788025856000 : ℝ) ≤ (47669467980541945134311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_264 : rowCell 2 264 ≤ (36576326136861772741193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16452608564796923639499 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47669467980541945134311 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_264_1
  · norm_num [gridPoint]

theorem exp_2_265_0 : expNegUpper (61909758202054825641589 / 734153456694068736000 : ℝ) ≤ (23834731117236308702167 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_265_1 : expNegUpper (30991423517266908561601 / 367076728347034368000 : ℝ) ≤ (6742546992868304426413 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_265 : rowCell 2 265 ≤ (33114022774115758970103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23834731117236308702167 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6742546992868304426413 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_265_1
  · norm_num [gridPoint]

theorem exp_2_266_0 : expNegUpper (93398157423257081424307 / 1106250895282821376000 : ℝ) ≤ (43152295599947241178407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1934001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_266_1 : expNegUpper (37403409160551523822041 / 442500358113128550400 : ℝ) ≤ (195274879769631894209981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1935509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_266 : rowCell 2 266 ≤ (7493285124755001319023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43152295599947241178407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (195274879769631894209981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_266_1
  · norm_num [gridPoint]

theorem exp_2_267_0 : expNegUpper (1212050011574598987951 / 14339135802289254400 : ℝ) ≤ (195274856655648172616097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1935509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_267_1 : expNegUpper (1516854439837841371939 / 17923919752861568000 : ℝ) ≤ (8834829845513653717167 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_267 : rowCell 2 267 ≤ (27124492587129790460653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (195274856655648172616097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8834829845513653717167 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_267_1
  · norm_num [gridPoint]

theorem exp_2_268_0 : expNegUpper (15745299620095763708767 / 186054428870815104000 : ℝ) ≤ (176696576184106614714413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1937021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_268_1 : expNegUpper (63055755102448077043121 / 744217715483260416000 : ℝ) ≤ (19981588275977429738061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (969269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_268 : rowCell 2 268 ≤ (12270738020257573376517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (176696576184106614714413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19981588275977429738061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_268_1
  · norm_num [gridPoint]

theorem exp_2_269_0 : expNegUpper (7600954231204470947843 / 89710523274019328000 : ℝ) ≤ (7992634381313196093373 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (969269 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_269_1 : expNegUpper (3804980001949039377321 / 44855261637009664000 : ℝ) ≤ (5783388966467342493323 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_269 : rowCell 2 269 ≤ (22199849585564283781971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7992634381313196093373 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5783388966467342493323 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_269_1
  · norm_num [gridPoint]

theorem exp_2_270_0 : expNegUpper (95554271401644658717041 / 1126447927778470144000 : ℝ) ≤ (18073088438239613956247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_270_1 : expNegUpper (191335164902554190059561 / 2252895855556940288000 : ℝ) ≤ (13074829724038701044683 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (121349 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_270 : rowCell 2 270 ≤ (2007753007559693375673 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18073088438239613956247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13074829724038701044683 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_270_1
  · norm_num [gridPoint]

theorem exp_2_271_0 : expNegUpper (9152269833477163926109 / 107764355598531072000 : ℝ) ≤ (32687070578392349185873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (121349 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_271_1 : expNegUpper (114539148639874727047 / 1347054444981638400 : ℝ) ≤ (59105988871613369218711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1943113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_271 : rowCell 2 271 ≤ (1815440583857521895517 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32687070578392349185873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59105988871613369218711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_271_1
  · norm_num [gridPoint]

theorem exp_2_272_0 : expNegUpper (2416140460895547443347 / 28415373973588998400 : ℝ) ≤ (59105982184165254625387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1943113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_272_1 : expNegUpper (193520824527096669733311 / 2273229917887119872000 : ℝ) ≤ (106856102141898956320427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1944647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_272 : rowCell 2 272 ≤ (8206082809758468956869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59105982184165254625387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106856102141898956320427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_272_1
  · norm_num [gridPoint]

theorem exp_2_273_0 : expNegUpper (194389263901498023221559 / 2283431206510842368000 : ℝ) ≤ (106856090159748595471031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1944647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_273_1 : expNegUpper (97310169665607110835839 / 1141715603255421184000 : ℝ) ≤ (12071470459598079568053 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (389237 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_273 : rowCell 2 273 ≤ (14834141868972434538893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (106856090159748595471031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12071470459598079568053 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_273_1
  · norm_num [gridPoint]

theorem exp_2_274_0 : expNegUpper (52131135355979139317 / 611641422250752000 : ℝ) ≤ (12071469118035860823889 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (389237 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_274_1 : expNegUpper (104386306197163116791 / 1223282844501504000 : ℝ) ≤ (21814967902019906501951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1947727 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_274 : rowCell 2 274 ≤ (6702583611791874932751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12071469118035860823889 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21814967902019906501951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_274_1
  · norm_num [gridPoint]

theorem exp_2_275_0 : expNegUpper (196598727914253689848397 / 2303902298675552768000 : ℝ) ≤ (21814965499156432889389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1947727 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_275_1 : expNegUpper (49208197221208795849179 / 575975574668888192000 : ℝ) ≤ (39415145051622318529957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (974637 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_275 : rowCell 2 275 ≤ (12111443112743574506871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21814965499156432889389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39415145051622318529957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_275_1
  · norm_num [gridPoint]

theorem exp_2_276_0 : expNegUpper (49427546220458105544891 / 578543025554135168000 : ℝ) ≤ (78830281497268335265399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (974637 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_276_1 : expNegUpper (39589148723803177328303 / 462834420443308134400 : ℝ) ≤ (35600525141074811324317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (78033 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_276 : rowCell 2 276 ≤ (10940419507129803061913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78830281497268335265399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35600525141074811324317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_276_1
  · norm_num [gridPoint]

theorem exp_2_277_0 : expNegUpper (13255075898666441077421 / 154964316270885580800 : ℝ) ≤ (35600521288913012682263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (78033 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_277_1 : expNegUpper (33177199719093600074431 / 387410790677213952000 : ℝ) ≤ (64297629442442249092869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97619 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_277 : rowCell 2 277 ≤ (2470171225201526445803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35600521288913012682263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64297629442442249092869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_277_1
  · norm_num [gridPoint]

theorem exp_2_278_0 : expNegUpper (14281899907220351323051 / 166770016015412992000 : ℝ) ≤ (32148811273257071384537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (97619 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_278_1 : expNegUpper (28597880423401567362999 / 333540032030825984000 : ℝ) ≤ (58052291952590272270737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953939 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_278 : rowCell 2 278 ≤ (4460932844513000866913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32148811273257071384537 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58052291952590272270737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_278_1
  · norm_num [gridPoint]

theorem exp_2_279_0 : expNegUpper (8042863021497439039713 / 93804741706961408000 : ℝ) ≤ (58052285781309618566179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953939 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_279_1 : expNegUpper (1006558237795513233269 / 11725592713370176000 : ℝ) ≤ (52403486731105736432591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (977751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_279 : rowCell 2 279 ≤ (8054534169213444309681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58052285781309618566179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52403486731105736432591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_279_1
  · norm_num [gridPoint]

theorem exp_2_280_0 : expNegUpper (8425044957557851470863 / 98144987476585152000 : ℝ) ≤ (13100870302319824897321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (977751 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_280_1 : expNegUpper (67480887364258424171357 / 785159899812681216000 : ℝ) ≤ (11823824157474257780633 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (195707 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_280 : rowCell 2 280 ≤ (7270124453153452920491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13100870302319824897321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11823824157474257780633 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_280_1
  · norm_num [gridPoint]

theorem exp_2_281_0 : expNegUpper (203335119025280943175439 / 2365863694507807232000 : ℝ) ≤ (9459058338005219459339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (195707 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_281_1 : expNegUpper (20357821655716749585087 / 236586369450780723200 : ℝ) ≤ (341415483277028475503 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_281 : rowCell 2 281 ≤ (3280427817264801207533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9459058338005219459339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341415483277028475503 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_281_1
  · norm_num [gridPoint]

theorem exp_2_282_0 : expNegUpper (20447370566145214634607 / 237627052788332595200 : ℝ) ≤ (10669232747783414390413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_282_1 : expNegUpper (204718320944617963393261 / 2376270527883325952000 : ℝ) ≤ (9625572084347796628699 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_282 : rowCell 2 282 ≤ (1183932321578179420319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10669232747783414390413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9625572084347796628699 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_282_1
  · norm_num [gridPoint]

theorem exp_2_283_0 : expNegUpper (68538949627413563847223 / 795566733188199936000 : ℝ) ≤ (9625571096478394552943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_283_1 : expNegUpper (17155248770622110155859 / 198891683297049984000 : ℝ) ≤ (3472949275377729006447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_283 : rowCell 2 283 ≤ (5340126983201032055719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9625571096478394552943 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3472949275377729006447 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_283_1
  · norm_num [gridPoint]

theorem exp_2_284_0 : expNegUpper (2067645586799852254913 / 23971527095516288000 : ℝ) ≤ (17364744610274887656183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_284_1 : expNegUpper (8280488778321928720443 / 95886108382065152000 : ℝ) ≤ (31320555249378077475083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_284 : rowCell 2 284 ≤ (4816428584583967476067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17364744610274887656183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31320555249378077475083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_284_1
  · norm_num [gridPoint]

theorem exp_2_285_0 : expNegUpper (29702406435289199274861 / 343946865406344704000 : ℝ) ≤ (7830138022664592524619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_285_1 : expNegUpper (14869002397764664181759 / 171973432703172352000 : ℝ) ≤ (28241002361437193366273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1964969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_285 : rowCell 2 285 ≤ (2171641031490443271229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7830138022664592524619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28241002361437193366273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_285_1
  · norm_num [gridPoint]

theorem exp_2_286_0 : expNegUpper (34845619662616141094819 / 403021040740492032000 : ℝ) ≤ (28240999537997762453057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1964969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_286_1 : expNegUpper (2790992500957002802667 / 32241683259239362560 : ℝ) ≤ (6364890487865285515009 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (983281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_286 : rowCell 2 286 ≤ (391589319040955650283 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28240999537997762453057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6364890487865285515009 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_286_1
  · norm_num [gridPoint]

theorem exp_2_287_0 : expNegUpper (8409407498333649086201 / 97145890773889863680 : ℝ) ≤ (12729779714064998940447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (983281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_287_1 : expNegUpper (6577732545612393740823 / 75895227167101456000 : ℝ) ≤ (11473936327732236595709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (984079 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_287 : rowCell 2 287 ≤ (3529913438587971435001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12729779714064998940447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11473936327732236595709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_287_1
  · norm_num [gridPoint]

theorem sum_2_256_2 : blockSum (rowCell 2) 256 2 ≤ (4791972508059043660581 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_256) (by simpa only [blockSum_one] using cell_2_257) (by norm_num)

theorem sum_2_258_2 : blockSum (rowCell 2) 258 2 ≤ (63034845364341023218191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_258) (by simpa only [blockSum_one] using cell_2_259) (by norm_num)

theorem sum_2_256_4 : blockSum (rowCell 2) 256 4 ≤ (139706405493285721787487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_256_2 sum_2_258_2 (by norm_num)

theorem sum_2_260_2 : blockSum (rowCell 2) 260 2 ≤ (25888927426521848854369 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_260) (by simpa only [blockSum_one] using cell_2_261) (by norm_num)

theorem sum_2_262_2 : blockSum (rowCell 2) 262 2 ≤ (663971861463501326441 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_262) (by simpa only [blockSum_one] using cell_2_263) (by norm_num)

theorem sum_2_260_4 : blockSum (rowCell 2) 260 4 ≤ (47136026993353891300481 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_260_2 sum_2_262_2 (by norm_num)

theorem sum_2_256_8 : blockSum (rowCell 2) 256 8 ≤ (233978459479993504388449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_256_4 sum_2_260_4 (by norm_num)

theorem sum_2_264_2 : blockSum (rowCell 2) 264 2 ≤ (1088911701734023932989 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_264) (by simpa only [blockSum_one] using cell_2_265) (by norm_num)

theorem sum_2_266_2 : blockSum (rowCell 2) 266 2 ≤ (11419526617229959147349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_266) (by simpa only [blockSum_one] using cell_2_267) (by norm_num)

theorem sum_2_264_4 : blockSum (rowCell 2) 264 4 ≤ (126787981997127327448041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_264_2 sum_2_266_2 (by norm_num)

theorem sum_2_268_2 : blockSum (rowCell 2) 268 2 ≤ (9348265125215886107001 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_268) (by simpa only [blockSum_one] using cell_2_269) (by norm_num)

theorem sum_2_270_2 : blockSum (rowCell 2) 270 2 ≤ (382319359141721527119 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_270) (by simpa only [blockSum_one] using cell_2_271) (by norm_num)

theorem sum_2_268_4 : blockSum (rowCell 2) 268 4 ≤ (16994652308050316649381 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_268_2 sum_2_270_2 (by norm_num)

theorem sum_2_264_8 : blockSum (rowCell 2) 264 8 ≤ (105880621768689455347473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_264_4 sum_2_268_4 (by norm_num)

theorem sum_2_256_16 : blockSum (rowCell 2) 256 16 ≤ (169929540624341479867961 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_256_8 sum_2_264_8 (by norm_num)

theorem sum_2_272_2 : blockSum (rowCell 2) 272 2 ≤ (31246307488489372452631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_272) (by simpa only [blockSum_one] using cell_2_273) (by norm_num)

theorem sum_2_274_2 : blockSum (rowCell 2) 274 2 ≤ (25516610336327324372373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_274) (by simpa only [blockSum_one] using cell_2_275) (by norm_num)

theorem sum_2_272_4 : blockSum (rowCell 2) 272 4 ≤ (14190729456204174206251 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_272_2 sum_2_274_2 (by norm_num)

theorem sum_2_276_2 : blockSum (rowCell 2) 276 2 ≤ (166568835263487270761 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_276) (by simpa only [blockSum_one] using cell_2_277) (by norm_num)

theorem sum_2_278_2 : blockSum (rowCell 2) 278 2 ≤ (16976399858239446043507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_278) (by simpa only [blockSum_one] using cell_2_279) (by norm_num)

theorem sum_2_276_4 : blockSum (rowCell 2) 276 4 ≤ (4724688033271919361079 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_276_2 sum_2_278_2 (by norm_num)

theorem sum_2_272_8 : blockSum (rowCell 2) 272 8 ≤ (23640105522748012928409 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_272_4 sum_2_276_4 (by norm_num)

theorem sum_2_280_2 : blockSum (rowCell 2) 280 2 ≤ (13830980087683055335557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_280) (by simpa only [blockSum_one] using cell_2_281) (by norm_num)

theorem sum_2_282_2 : blockSum (rowCell 2) 282 2 ≤ (5629894295545964578657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_282) (by simpa only [blockSum_one] using cell_2_283) (by norm_num)

theorem sum_2_280_4 : blockSum (rowCell 2) 280 4 ≤ (25090768678774984492871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_280_2 sum_2_282_2 (by norm_num)

theorem sum_2_284_2 : blockSum (rowCell 2) 284 2 ≤ (366388425902594160741 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_284) (by simpa only [blockSum_one] using cell_2_285) (by norm_num)

theorem sum_2_286_2 : blockSum (rowCell 2) 286 2 ≤ (7445806628997527937831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_286) (by simpa only [blockSum_one] using cell_2_287) (by norm_num)

theorem sum_2_284_4 : blockSum (rowCell 2) 284 4 ≤ (4151379319140595489089 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_284_2 sum_2_286_2 (by norm_num)

theorem sum_2_280_8 : blockSum (rowCell 2) 280 8 ≤ (41696285955337366449227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_280_4 sum_2_284_4 (by norm_num)

theorem sum_2_272_16 : blockSum (rowCell 2) 272 16 ≤ (136256708046329418162863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_272_8 sum_2_280_8 (by norm_num)

theorem sum_2_256_32 : blockSum (rowCell 2) 256 32 ≤ (815974870543695337634707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_256_16 sum_2_272_16 (by norm_num)

#print axioms sum_2_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
