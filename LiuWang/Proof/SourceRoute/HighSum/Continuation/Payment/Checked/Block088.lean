import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_256_0 : expNegUpper (709175303050941169969 / 8254356677696322000 : ℝ) ≤ (48742222898178482443877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_256_1 : expNegUpper (36348595522086479708419 / 422623061898051686400 : ℝ) ≤ (44464483119876462513859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_256 : rowCell 5 256 ≤ (3398358371618252341279 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (48742222898178482443877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44464483119876462513859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_256_1
  · norm_num [gridPoint]

theorem exp_5_257_0 : expNegUpper (36517786667141131800859 / 424590237044379750400 : ℝ) ≤ (44464476663849490669471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_257_1 : expNegUpper (91392233923443829831943 / 1061475592610949376000 : ℝ) ≤ (40552018188817876456137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_257 : rowCell 5 257 ≤ (6199479186663598604137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44464476663849490669471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40552018188817876456137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_257_1
  · norm_num [gridPoint]

theorem exp_5_258_0 : expNegUpper (91816647933260776147447 / 1066404949629647104000 : ℝ) ≤ (20276006177615903543377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1959423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_258_1 : expNegUpper (183830268190273643493733 / 2132809899259294208000 : ℝ) ≤ (4621828599737229275039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_258 : rowCell 5 258 ≤ (1130662465145574891513 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20276006177615903543377 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4621828599737229275039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_258_1
  · norm_num [gridPoint]

theorem exp_5_259_0 : expNegUpper (7387279006633090644517 / 85707658064097792000 : ℝ) ≤ (36974623527937686490729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_259_1 : expNegUpper (1848803886329289967607 / 21426914516024448000 : ℝ) ≤ (4213063998795406600541 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (122641 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_259 : rowCell 5 259 ≤ (161062064461885053653 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36974623527937686490729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4213063998795406600541 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_259_1
  · norm_num [gridPoint]

theorem exp_5_260_0 : expNegUpper (46433745306490361796863 / 538148960562837632000 : ℝ) ≤ (33704507230645472296643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (122641 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_260_1 : expNegUpper (185934839167192366193851 / 2152595842251350528000 : ℝ) ≤ (479938843310436962707 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12273 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_260 : rowCell 5 260 ≤ (4697607534203985275557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33704507230645472296643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (479938843310436962707 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_260_1
  · norm_num [gridPoint]

theorem exp_5_261_0 : expNegUpper (186792324039262742247539 / 2162523071206011392000 : ℝ) ≤ (3071608167395198173439 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12273 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_261_1 : expNegUpper (747974519141609594089 / 8650092284824045568 : ℝ) ≤ (6996455195229441330207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1965109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_261 : rowCell 5 261 ≤ (856119093399917750461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3071608167395198173439 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6996455195229441330207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_261_1
  · norm_num [gridPoint]

theorem exp_5_262_0 : expNegUpper (751416054392279192089 / 8689892553865709568 : ℝ) ≤ (13992908450430060344669 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1965109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_262_1 : expNegUpper (188056770479897740474961 / 2172473138466427392000 : ℝ) ≤ (25492081110319831942697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (983271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_262 : rowCell 5 262 ≤ (3899656369524236565417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13992908450430060344669 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25492081110319831942697 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_262_1
  · norm_num [gridPoint]

theorem exp_5_263_0 : expNegUpper (188920059894721261240649 / 2182446044032598528000 : ℝ) ≤ (5098415521653462152007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (983271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_263_1 : expNegUpper (23640533905377129847631 / 272805755504074816000 : ℝ) ≤ (2901872559704688789483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (98399 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_263 : rowCell 5 263 ≤ (110992576120989956499 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5098415521653462152007 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2901872559704688789483 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_263_1
  · norm_num [gridPoint]

theorem exp_5_264_0 : expNegUpper (949952364607778893159 / 10962208939522624000 : ℝ) ≤ (580374432936399477613 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (98399 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_264_1 : expNegUpper (7607845682683957606783 / 87697671516180992000 : ℝ) ≤ (845449839566346665763 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_264 : rowCell 5 264 ≤ (404266381290066188073 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (580374432936399477613 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (845449839566346665763 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_264_1
  · norm_num [gridPoint]

theorem exp_5_265_0 : expNegUpper (191065262670911996924767 / 2202460370082206208000 : ℝ) ≤ (10568121569047302523143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969423 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_265_1 : expNegUpper (95636196472241045684803 / 1101230185041103104000 : ℝ) ≤ (19239092986293503369309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (197087 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_265 : rowCell 5 265 ≤ (2944205784906430120607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10568121569047302523143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19239092986293503369309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_265_1
  · norm_num [gridPoint]

theorem exp_5_266_0 : expNegUpper (96072219567564281424307 / 1106250895282821376000 : ℝ) ≤ (480977260366636178663 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1970871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_266_1 : expNegUpper (38470606773501027822041 / 442500358113128550400 : ℝ) ≤ (17508108905661939534769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_266 : rowCell 5 266 ≤ (2679638789500162393437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (480977260366636178663 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17508108905661939534769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_266_1
  · norm_num [gridPoint]

theorem exp_5_267_0 : expNegUpper (1246632337461574987951 / 14339135802289254400 : ℝ) ≤ (4377026646644820925333 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_267_1 : expNegUpper (1559984474423441371939 / 17923919752861568000 : ℝ) ≤ (497785803889186046909 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (98689 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_267 : rowCell 5 267 ≤ (97530979192076674029 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4377026646644820925333 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (497785803889186046909 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_267_1
  · norm_num [gridPoint]

theorem exp_5_268_0 : expNegUpper (48578998044374331126301 / 558163286612445312000 : ℝ) ≤ (1592914363356077199359 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (98689 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_268_1 : expNegUpper (194527525819825511129363 / 2232653146449781248000 : ℝ) ≤ (1811152550124551817399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_268 : rowCell 5 268 ≤ (2218134434398847339443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1592914363356077199359 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1811152550124551817399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_268_1
  · norm_num [gridPoint]

theorem exp_5_269_0 : expNegUpper (7816335549613072547843 / 89710523274019328000 : ℝ) ≤ (3622304629059536298129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975241 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_269_1 : expNegUpper (3912427936676002577321 / 44855261637009664000 : ℝ) ≤ (3294105689222266630171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_269 : rowCell 5 269 ≤ (504350854371504400839 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3622304629059536298129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3294105689222266630171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_269_1
  · norm_num [gridPoint]

theorem exp_5_270_0 : expNegUpper (98252605993685618717041 / 1126447927778470144000 : ℝ) ≤ (13176421058300087543609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_270_1 : expNegUpper (196719697862769230059561 / 2252895855556940288000 : ℝ) ≤ (2994957570409051520923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989089 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_270 : rowCell 5 270 ≤ (1834416449027717755317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13176421058300087543609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2994957570409051520923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_270_1
  · norm_num [gridPoint]

theorem exp_5_271_0 : expNegUpper (197606471910969242448289 / 2263051467569152512000 : ℝ) ≤ (11979828751146493778223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989089 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_271_1 : expNegUpper (2472780486238393267987 / 28288143344614406400 : ℝ) ≤ (2722357343364445539541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_271 : rowCell 5 271 ≤ (416911712261310031359 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11979828751146493778223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2722357343364445539541 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_271_1
  · norm_num [gridPoint]

theorem exp_5_272_0 : expNegUpper (2483902231293243443347 / 28415373973588998400 : ℝ) ≤ (2722356998679247578927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979653 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_272_1 : expNegUpper (198929629935045469733311 / 2273229917887119872000 : ℝ) ≤ (395841702438994301217 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1981133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_272 : rowCell 5 272 ≤ (303139037473450384867 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2722356998679247578927 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (395841702438994301217 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_272_1
  · norm_num [gridPoint]

theorem exp_5_273_0 : expNegUpper (199822341757180583221559 / 2283431206510842368000 : ℝ) ≤ (9896041319192297707119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1981133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_273_1 : expNegUpper (100020640481514950835839 / 1141715603255421184000 : ℝ) ≤ (2247815319947976054463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991309 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_273 : rowCell 5 273 ≤ (688639537289428389619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9896041319192297707119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2247815319947976054463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_273_1
  · norm_num [gridPoint]

theorem exp_5_274_0 : expNegUpper (160749577331576969951 / 1834924266752256000 : ℝ) ≤ (140488440024859903453 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991309 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_274_1 : expNegUpper (321851843160581446373 / 3669848533504512000 : ℝ) ≤ (8167383805705572429707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1984107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_274 : rowCell 5 274 ≤ (625611867032228947923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (140488440024859903453 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8167383805705572429707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_274_1
  · norm_num [gridPoint]

theorem exp_5_275_0 : expNegUpper (202056078217670009848397 / 2303902298675552768000 : ℝ) ≤ (8167382798991715058909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1984107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_275_1 : expNegUpper (50569500741096155849179 / 575975574668888192000 : ℝ) ≤ (370867898621012820981 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_275 : rowCell 5 275 ≤ (568226649483448887829 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8167382798991715058909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (370867898621012820981 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_275_1
  · norm_num [gridPoint]

theorem exp_5_276_0 : expNegUpper (50794917852278905544891 / 578543025554135168000 : ℝ) ≤ (1483471413252077393243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_276_1 : expNegUpper (40680618784486441328303 / 462834420443308134400 : ℝ) ≤ (3367364163154499939147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1987099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_276 : rowCell 5 276 ≤ (1031982781590379575261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1483471413252077393243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3367364163154499939147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_276_1
  · norm_num [gridPoint]

theorem exp_5_277_0 : expNegUpper (40861552246229339232263 / 464892948812656742400 : ℝ) ≤ (6734727510822526208283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1987099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_277_1 : expNegUpper (102266342420922400223293 / 1162232372031641856000 : ℝ) ≤ (6113587393987834319033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (994301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_277 : rowCell 5 277 ≤ (936910666266693780211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6734727510822526208283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6113587393987834319033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_277_1
  · norm_num [gridPoint]

theorem exp_5_278_0 : expNegUpper (102720178838050939261357 / 1167390112107890944000 : ℝ) ≤ (244543466409895944529 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (994301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_278_1 : expNegUpper (205666785714961051540993 / 2334780224215781888000 : ℝ) ≤ (5548530760335777735913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_278 : rowCell 5 278 ≤ (850412079992545274577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (244543466409895944529 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5548530760335777735913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_278_1
  · norm_num [gridPoint]

theorem exp_5_279_0 : expNegUpper (8263098829452792639713 / 93804741706961408000 : ℝ) ≤ (5548530100277184354029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_279_1 : expNegUpper (1034027032670598033269 / 11725592713370176000 : ℝ) ≤ (5034615675153868671583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1991621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_279 : rowCell 5 279 ≤ (154346499647893000093 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5548530100277184354029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5034615675153868671583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_279_1
  · norm_num [gridPoint]

theorem exp_5_280_0 : expNegUpper (25964888800517394412589 / 294434962429755456000 : ℝ) ≤ (5034615081494322319619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1991621 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_280_1 : expNegUpper (207948557291659112514071 / 2355479699438043648000 : ℝ) ≤ (2283661462988072988453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_280 : rowCell 5 280 ≤ (175045486561481283733 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5034615081494322319619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2283661462988072988453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_280_1
  · norm_num [gridPoint]

theorem exp_5_281_0 : expNegUpper (208865286671898543175439 / 2365863694507807232000 : ℝ) ≤ (4567322392140054523047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_281_1 : expNegUpper (20909624797991821585087 / 236586369450780723200 : ℝ) ≤ (2071260866341760544013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_281 : rowCell 5 281 ≤ (635129658832716029741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4567322392140054523047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2071260866341760544013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_281_1
  · norm_num [gridPoint]

theorem exp_5_282_0 : expNegUpper (21001600953193662634607 / 237627052788332595200 : ℝ) ≤ (517815156591897760909 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (997329 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_282_1 : expNegUpper (210248488591235563393261 / 2376270527883325952000 : ℝ) ≤ (469554679573339207921 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1996183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_282 : rowCell 5 282 ≤ (287999582173025037889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (517815156591897760909 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (469554679573339207921 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_282_1
  · norm_num [gridPoint]

theorem exp_5_283_0 : expNegUpper (211171288976592051541669 / 2386700199564599808000 : ℝ) ≤ (3756437005169262974663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1996183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_283_1 : expNegUpper (52851322279487450467577 / 596675049891149952000 : ℝ) ≤ (681124354518790301873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_283 : rowCell 5 283 ≤ (261131880368338373407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3756437005169262974663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (681124354518790301873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_283_1
  · norm_num [gridPoint]

theorem exp_5_284_0 : expNegUpper (2123311349982034654913 / 23971527095516288000 : ℝ) ≤ (3405621384874006747473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997713 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_284_1 : expNegUpper (8502666382095983120443 / 95886108382065152000 : ℝ) ≤ (3086925528018410115751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_284 : rowCell 5 284 ≤ (59180294254466511181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3405621384874006747473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3086925528018410115751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_284_1
  · norm_num [gridPoint]

theorem exp_5_285_0 : expNegUpper (213495557589109514924027 / 2407628057844412928000 : ℝ) ≤ (1543462589817945734157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_285_1 : expNegUpper (106866304943461769272313 / 1203814028922206464000 : ℝ) ≤ (559494681112610940207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (400157 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_285 : rowCell 5 285 ≤ (107273907899265261087 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1543462589817945734157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (559494681112610940207 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_285_1
  · norm_num [gridPoint]

theorem exp_5_286_0 : expNegUpper (107332283370824423284457 / 1209063122221476096000 : ℝ) ≤ (8742103414330347577 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (400157 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_286_1 : expNegUpper (8596126004554413208001 / 96725049777718087680 : ℝ) ≤ (2534640921098480361147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250291 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_286 : rowCell 5 286 ≤ (388822544449035419827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8742103414330347577 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2534640921098480361147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_286_1
  · norm_num [gridPoint]

theorem exp_5_287_0 : expNegUpper (8633526897926404286201 / 97145890773889863680 : ℝ) ≤ (506928127996138317407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (250291 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_287_1 : expNegUpper (6752446569548393740823 / 75895227167101456000 : ℝ) ≤ (4484439802875918287 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (16031 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_287 : rowCell 5 287 ≤ (11008033591995808137 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (506928127996138317407 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4484439802875918287 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_287_1
  · norm_num [gridPoint]

theorem sum_5_256_2 : blockSum (rowCell 5) 256 2 ≤ (2599239185980020657339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_256) (by simpa only [blockSum_one] using cell_5_257) (by norm_num)

theorem sum_5_258_2 : blockSum (rowCell 5) 258 2 ≤ (10807298388508196174461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_258) (by simpa only [blockSum_one] using cell_5_259) (by norm_num)

theorem sum_5_256_4 : blockSum (rowCell 5) 256 4 ≤ (5950873579602074865289 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_256_2 sum_5_258_2 (by norm_num)

theorem sum_5_260_2 : blockSum (rowCell 5) 260 2 ≤ (4489101500601787013931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_260) (by simpa only [blockSum_one] using cell_5_261) (by norm_num)

theorem sum_5_262_2 : blockSum (rowCell 5) 262 2 ≤ (1490283761079183034677 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_262) (by simpa only [blockSum_one] using cell_5_263) (by norm_num)

theorem sum_5_260_4 : blockSum (rowCell 5) 260 4 ≤ (16429621806599489201247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_260_2 sum_5_262_2 (by norm_num)

theorem sum_5_256_8 : blockSum (rowCell 5) 256 8 ≤ (40233116125007788662403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_256_4 sum_5_260_4 (by norm_num)

theorem sum_5_264_2 : blockSum (rowCell 5) 264 2 ≤ (6178336835226959625191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_264) (by simpa only [blockSum_one] using cell_5_265) (by norm_num)

theorem sum_5_266_2 : blockSum (rowCell 5) 266 2 ≤ (2558956634651039622081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_266) (by simpa only [blockSum_one] using cell_5_267) (by norm_num)

theorem sum_5_264_4 : blockSum (rowCell 5) 264 4 ≤ (11296250104529038869353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_264_2 sum_5_266_2 (by norm_num)

theorem sum_5_268_2 : blockSum (rowCell 5) 268 2 ≤ (4235537851884864942799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_268) (by simpa only [blockSum_one] using cell_5_269) (by norm_num)

theorem sum_5_270_2 : blockSum (rowCell 5) 270 2 ≤ (3502063298072957880753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_270) (by simpa only [blockSum_one] using cell_5_271) (by norm_num)

theorem sum_5_268_4 : blockSum (rowCell 5) 268 4 ≤ (60450008984045490809 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_268_2 sum_5_270_2 (by norm_num)

theorem sum_5_264_8 : blockSum (rowCell 5) 264 8 ≤ (3806770250897372338581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_264_4 sum_5_268_4 (by norm_num)

theorem sum_5_256_16 : blockSum (rowCell 5) 256 16 ≤ (14816741844873662588827 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_256_8 sum_5_264_8 (by norm_num)

theorem sum_5_272_2 : blockSum (rowCell 5) 272 2 ≤ (2892974261946108703573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_272) (by simpa only [blockSum_one] using cell_5_273) (by norm_num)

theorem sum_5_274_2 : blockSum (rowCell 5) 274 2 ≤ (149229814564459729469 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_274) (by simpa only [blockSum_one] using cell_5_275) (by norm_num)

theorem sum_5_272_4 : blockSum (rowCell 5) 272 4 ≤ (5280651294977464375077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_272_2 sum_5_274_2 (by norm_num)

theorem sum_5_276_2 : blockSum (rowCell 5) 276 2 ≤ (123055840491067084717 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_276) (by simpa only [blockSum_one] using cell_5_277) (by norm_num)

theorem sum_5_278_2 : blockSum (rowCell 5) 278 2 ≤ (811072289116005137521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_278) (by simpa only [blockSum_one] using cell_5_279) (by norm_num)

theorem sum_5_276_4 : blockSum (rowCell 5) 276 4 ≤ (1795519013044541815257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_276_2 sum_5_278_2 (by norm_num)

theorem sum_5_272_8 : blockSum (rowCell 5) 272 8 ≤ (8871689321066548005591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_272_4 sum_5_276_4 (by norm_num)

theorem sum_5_280_2 : blockSum (rowCell 5) 280 2 ≤ (1335311605078641164673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_280) (by simpa only [blockSum_one] using cell_5_281) (by norm_num)

theorem sum_5_282_2 : blockSum (rowCell 5) 282 2 ≤ (17160358204417606603 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_282) (by simpa only [blockSum_one] using cell_5_283) (by norm_num)

theorem sum_5_280_4 : blockSum (rowCell 5) 280 4 ≤ (486714906032273597453 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_280_2 sum_5_282_2 (by norm_num)

theorem sum_5_284_2 : blockSum (rowCell 5) 284 2 ≤ (225634496408198283449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_284) (by simpa only [blockSum_one] using cell_5_285) (by norm_num)

theorem sum_5_286_2 : blockSum (rowCell 5) 286 2 ≤ (741079619392901280211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_286) (by simpa only [blockSum_one] using cell_5_287) (by norm_num)

theorem sum_5_284_4 : blockSum (rowCell 5) 284 4 ≤ (1643617605025694414007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_284_2 sum_5_286_2 (by norm_num)

theorem sum_5_280_8 : blockSum (rowCell 5) 280 8 ≤ (509649016898382800159 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_280_4 sum_5_284_4 (by norm_num)

theorem sum_5_272_16 : blockSum (rowCell 5) 272 16 ≤ (12948881456253610406863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_272_8 sum_5_280_8 (by norm_num)

theorem sum_5_256_32 : blockSum (rowCell 5) 256 32 ≤ (72215848835748260762171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_256_16 sum_5_272_16 (by norm_num)

#print axioms sum_5_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
