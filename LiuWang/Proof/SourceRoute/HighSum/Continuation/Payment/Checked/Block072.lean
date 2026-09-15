import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_256_0 : expNegUpper (705091895199421169969 / 8254356677696322000 : ℝ) ≤ (19984332268204305422991 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (974531 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_256_1 : expNegUpper (36140010489043330908419 / 422623061898051686400 : ℝ) ≤ (7283811442351091591137 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_256 : rowCell 4 256 ≤ (11140522598939764026347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19984332268204305422991 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7283811442351091591137 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_256_1
  · norm_num [gridPoint]

theorem exp_4_257_0 : expNegUpper (36308230736188632600859 / 424590237044379750400 : ℝ) ≤ (9104763009098279436901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975239 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_257_1 : expNegUpper (90869557718449269831943 / 1061475592610949376000 : ℝ) ≤ (33176562129654058610569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (19519 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_257 : rowCell 4 257 ≤ (317185919518610150503 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9104763009098279436901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33176562129654058610569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_257_1
  · norm_num [gridPoint]

theorem exp_4_258_0 : expNegUpper (91291544483492840147447 / 1066404949629647104000 : ℝ) ≤ (66353114917208631357053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (19519 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_258_1 : expNegUpper (182782488535511147493733 / 2132809899259294208000 : ℝ) ≤ (60430818787719221560413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976663 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_258 : rowCell 4 258 ≤ (462259917660188852793 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66353114917208631357053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (60430818787719221560413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_258_1
  · norm_num [gridPoint]

theorem exp_4_259_0 : expNegUpper (7345173640860720724517 / 85707658064097792000 : ℝ) ≤ (30215405178914089017481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (976663 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_259_1 : expNegUpper (1838301817333931247607 / 21426914516024448000 : ℝ) ≤ (6877977393705572174243 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_259 : rowCell 4 259 ≤ (841905531245361144593 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30215405178914089017481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6877977393705572174243 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_259_1
  · norm_num [gridPoint]

theorem exp_4_260_0 : expNegUpper (46169979959219705796863 / 538148960562837632000 : ℝ) ≤ (55023811544563212385361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_260_1 : expNegUpper (184882205022883118193851 / 2152595842251350528000 : ℝ) ≤ (25044297947547931805809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (61131 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_260 : rowCell 4 260 ≤ (7664891187428498890401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (55023811544563212385361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25044297947547931805809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_260_1
  · norm_num [gridPoint]

theorem exp_4_261_0 : expNegUpper (185734835405406742247539 / 2162523071206011392000 : ℝ) ≤ (25044294517810420424581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (61131 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_261_1 : expNegUpper (743754273585279098089 / 8650092284824045568 : ℝ) ≤ (45585169611119620080247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1957633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_261 : rowCell 4 261 ≤ (436038527338303036991 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25044294517810420424581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45585169611119620080247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_261_1
  · norm_num [gridPoint]

theorem exp_4_262_0 : expNegUpper (747176390877761688089 / 8689892553865709568 : ℝ) ≤ (45585163425493323943213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1957633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_262_1 : expNegUpper (186999281846041740474961 / 2172473138466427392000 : ℝ) ≤ (2592302098096736134539 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (979539 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_262 : rowCell 4 262 ≤ (6348639040641322397069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45585163425493323943213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2592302098096736134539 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_262_1
  · norm_num [gridPoint]

theorem exp_4_263_0 : expNegUpper (8167726816144283010463 / 94888958436199936000 : ℝ) ≤ (41476827992775231713327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (979539 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_263_1 : expNegUpper (1022088887849932949897 / 11861119804524992000 : ℝ) ≤ (37729896892710425698781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_263 : rowCell 4 263 ≤ (1443956385235375860503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41476827992775231713327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37729896892710425698781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_263_1
  · norm_num [gridPoint]

theorem exp_4_264_0 : expNegUpper (944628512766898253159 / 10962208939522624000 : ℝ) ≤ (4716236483242139318061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_264_1 : expNegUpper (7565351957747847526783 / 87697671516180992000 : ℝ) ≤ (2144590426672844476713 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_264 : rowCell 4 264 ≤ (5253464983908982225471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4716236483242139318061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2144590426672844476713 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_264_1
  · norm_num [gridPoint]

theorem exp_4_265_0 : expNegUpper (189998065057962492924767 / 2202460370082206208000 : ℝ) ≤ (3431344229671086468873 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980991 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_265_1 : expNegUpper (95103811288152981684803 / 1101230185041103104000 : ℝ) ≤ (3119912879926103504509 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_265 : rowCell 4 265 ≤ (1194308885817216241461 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3431344229671086468873 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3119912879926103504509 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_265_1
  · norm_num [gridPoint]

theorem exp_4_266_0 : expNegUpper (95537407138702841424307 / 1106250895282821376000 : ℝ) ≤ (6239824943540549486883 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_266_1 : expNegUpper (38257167250911127022041 / 442500358113128550400 : ℝ) ≤ (2836094302007574360341 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (245613 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_266 : rowCell 4 266 ≤ (2171586825218582863421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6239824943540549486883 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2836094302007574360341 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_266_1
  · norm_num [gridPoint]

theorem exp_4_267_0 : expNegUpper (1239715872284179787951 / 14339135802289254400 : ℝ) ≤ (14180469671690263134731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (245613 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_267_1 : expNegUpper (1551358467506321371939 / 17923919752861568000 : ℝ) ≤ (25775056463120094011189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491593 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_267 : rowCell 4 267 ≤ (3947645452018757633767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14180469671690263134731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25775056463120094011189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_267_1
  · norm_num [gridPoint]

theorem exp_4_268_0 : expNegUpper (48310378207556923126301 / 558163286612445312000 : ℝ) ≤ (25775053151816803317269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491593 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_268_1 : expNegUpper (193455473717329255129363 / 2232653146449781248000 : ℝ) ≤ (23419629140261506805057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393569 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_268 : rowCell 4 268 ≤ (3587320431085722163227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25775053151816803317269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23419629140261506805057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_268_1
  · norm_num [gridPoint]

theorem exp_4_269_0 : expNegUpper (7773259285931352227843 / 89710523274019328000 : ℝ) ≤ (23419626158652946250873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393569 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_269_1 : expNegUpper (3890938349730609937321 / 44855261637009664000 : ℝ) ≤ (21274653649012292391419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_269 : rowCell 4 269 ≤ (1629573519295981950517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23419626158652946250873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21274653649012292391419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_269_1
  · norm_num [gridPoint]

theorem exp_4_270_0 : expNegUpper (97712939075277426717041 / 1126447927778470144000 : ℝ) ≤ (10637325482411145390213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_270_1 : expNegUpper (195642791270726222059561 / 2252895855556940288000 : ℝ) ≤ (19321807041733444468303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (492701 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_270 : rowCell 4 270 ≤ (370041273902285559907 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10637325482411145390213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19321807041733444468303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_270_1
  · norm_num [gridPoint]

theorem exp_4_271_0 : expNegUpper (196524710829379482448289 / 2263051467569152512000 : ℝ) ≤ (19321804625786101889317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (492701 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_271_1 : expNegUpper (2459288813278188467987 / 28288143344614406400 : ℝ) ≤ (2193039265826614800887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_271 : rowCell 4 271 ≤ (268831050132850316851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19321804625786101889317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2193039265826614800887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_271_1
  · norm_num [gridPoint]

theorem exp_4_272_0 : expNegUpper (2470349877213704243347 / 28415373973588998400 : ℝ) ≤ (17544311952541175329123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_272_1 : expNegUpper (197847868853455709733311 / 2273229917887119872000 : ℝ) ≤ (15926821369623846393699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (986891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_272 : rowCell 4 272 ≤ (488149022714723503333 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17544311952541175329123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15926821369623846393699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_272_1
  · norm_num [gridPoint]

theorem exp_4_273_0 : expNegUpper (198735726186044071221559 / 2283431206510842368000 : ℝ) ≤ (3981704853401193429197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (986891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_273_1 : expNegUpper (99478546318333382835839 / 1141715603255421184000 : ℝ) ≤ (2891056124441393645951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_273 : rowCell 4 273 ≤ (1107745015514696573677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3981704853401193429197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2891056124441393645951 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_273_1
  · norm_num [gridPoint]

theorem exp_4_274_0 : expNegUpper (159878343078849059551 / 1834924266752256000 : ℝ) ≤ (2891055772544279784367 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_274_1 : expNegUpper (320113258246763027173 / 3669848533504512000 : ℝ) ≤ (6558420975850964690163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_274 : rowCell 4 274 ≤ (2010583821615043308253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2891055772544279784367 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6558420975850964690163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_274_1
  · norm_num [gridPoint]

theorem exp_4_275_0 : expNegUpper (200964608156986745848397 / 2303902298675552768000 : ℝ) ≤ (6558420184658128437963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_275_1 : expNegUpper (50297240037118683849179 / 575975574668888192000 : ℝ) ≤ (2974938725180462472099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_275 : rowCell 4 275 ≤ (456058150734622917529 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6558420184658128437963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2974938725180462472099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_275_1
  · norm_num [gridPoint]

theorem exp_4_276_0 : expNegUpper (50521443525914745544891 / 578543025554135168000 : ℝ) ≤ (5949876738945003069473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989141 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_276_1 : expNegUpper (40462324772349788528303 / 462834420443308134400 : ℝ) ≤ (2698319386967554784407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_276 : rowCell 4 276 ≤ (1654796210668497833621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5949876738945003069473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2698319386967554784407 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_276_1
  · norm_num [gridPoint]

theorem exp_4_277_0 : expNegUpper (40642287336183336032263 / 464892948812656742400 : ℝ) ≤ (10793276268754017393229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_277_1 : expNegUpper (101719393768194080223293 / 1162232372031641856000 : ℝ) ≤ (9787592785581421619999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (247663 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_277 : rowCell 4 277 ≤ (1500775462066681217341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10793276268754017393229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9787592785581421619999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_277_1
  · norm_num [gridPoint]

theorem exp_4_278_0 : expNegUpper (102170802940549243261357 / 1167390112107890944000 : ℝ) ≤ (4893795817943803451903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (247663 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_278_1 : expNegUpper (204570461164731035540993 / 2334780224215781888000 : ℝ) ≤ (4436865635782750133647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_278 : rowCell 4 278 ≤ (680400216221890119909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4893795817943803451903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4436865635782750133647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_278_1
  · norm_num [gridPoint]

theorem exp_4_279_0 : expNegUpper (8219051667861721919713 / 93804741706961408000 : ℝ) ≤ (8873730238397995202557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_279_1 : expNegUpper (1028533273695581073269 / 11725592713370176000 : ℝ) ≤ (8043500548489967890477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248043 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_279 : rowCell 4 279 ≤ (1233619668054405363399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8873730238397995202557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8043500548489967890477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_279_1
  · norm_num [gridPoint]

theorem exp_4_280_0 : expNegUpper (25826938014948626412589 / 294434962429755456000 : ℝ) ≤ (4021749810107967050529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248043 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_280_1 : expNegUpper (206847378251882344514071 / 2355479699438043648000 : ℝ) ≤ (1822354965567136428133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_280 : rowCell 4 280 ≤ (1118090264332615812657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4021749810107967050529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1822354965567136428133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_280_1
  · norm_num [gridPoint]

theorem exp_4_281_0 : expNegUpper (207759253142575023175439 / 2365863694507807232000 : ℝ) ≤ (728941902839700240771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_281_1 : expNegUpper (20799264169536807185087 / 236586369450780723200 : ℝ) ≤ (41279126517353023987 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (993701 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_281 : rowCell 4 281 ≤ (1013168743415815811961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (728941902839700240771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41279126517353023987 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_281_1
  · norm_num [gridPoint]

theorem exp_4_282_0 : expNegUpper (20890754875783973034607 / 237627052788332595200 : ℝ) ≤ (6604659493848336306683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (993701 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_282_1 : expNegUpper (209142455061912043393261 / 2376270527883325952000 : ℝ) ≤ (5982989442098149264847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1988937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_282 : rowCell 4 282 ≤ (917902669625058617297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6604659493848336306683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5982989442098149264847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_282_1
  · norm_num [gridPoint]

theorem exp_4_283_0 : expNegUpper (210060400957721779541669 / 2386700199564599808000 : ℝ) ≤ (5982988769586581672177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1988937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_283_1 : expNegUpper (52574207085963226467577 / 596675049891149952000 : ℝ) ≤ (1083744270930795077431 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_283 : rowCell 4 283 ≤ (415711472991780584071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5982988769586581672177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1083744270930795077431 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_283_1
  · norm_num [gridPoint]

theorem exp_4_284_0 : expNegUpper (2112178197345598174913 / 23971527095516288000 : ℝ) ≤ (5418720750874255250567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_284_1 : expNegUpper (8458230861341172240443 / 95886108382065152000 : ℝ) ≤ (981333914173052662581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1992021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_284 : rowCell 4 284 ≤ (376468369489556440749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5418720750874255250567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (981333914173052662581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_284_1
  · norm_num [gridPoint]

theorem exp_4_285_0 : expNegUpper (212379815080692490924027 / 2407628057844412928000 : ℝ) ≤ (613333628611636256173 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1992021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_285_1 : expNegUpper (106309647311639945272313 / 1203814028922206464000 : ℝ) ≤ (2221052370753378859961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (199357 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_285 : rowCell 4 285 ≤ (85215122828311405369 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (613333628611636256173 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2221052370753378859961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_285_1
  · norm_num [gridPoint]

theorem exp_4_286_0 : expNegUpper (4642312978009966229759 / 52567961835716352000 : ℝ) ≤ (888420851020873068929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (199357 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_286_1 : expNegUpper (371804187139901402087 / 4205436946857308160 : ℝ) ≤ (4020715453673856230929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_286 : rowCell 4 286 ≤ (24684656659147600909 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (888420851020873068929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4020715453673856230929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_286_1
  · norm_num [gridPoint]

theorem exp_4_287_0 : expNegUpper (8588703018007853246201 / 97145890773889863680 : ℝ) ≤ (2010357508611575631343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995123 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_287_1 : expNegUpper (6717503764761193740823 / 75895227167101456000 : ℝ) ≤ (3638572341454650092671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (49917 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_287 : rowCell 4 287 ≤ (13963052889644289673 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2010357508611575631343 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3638572341454650092671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_287_1
  · norm_num [gridPoint]

theorem sum_4_256_2 : blockSum (rowCell 4) 256 2 ≤ (21290472023535288842443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_256) (by simpa only [blockSum_one] using cell_4_257) (by norm_num)

theorem sum_4_258_2 : blockSum (rowCell 4) 258 2 ≤ (1766425366565738850179 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_258) (by simpa only [blockSum_one] using cell_4_259) (by norm_num)

theorem sum_4_256_4 : blockSum (rowCell 4) 256 4 ≤ (38954725689192677344233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_256_2 sum_4_258_2 (by norm_num)

theorem sum_4_260_2 : blockSum (rowCell 4) 260 2 ≤ (14641507624841347482257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_260) (by simpa only [blockSum_one] using cell_4_261) (by norm_num)

theorem sum_4_262_2 : blockSum (rowCell 4) 262 2 ≤ (12124464581582825839081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_262) (by simpa only [blockSum_one] using cell_4_263) (by norm_num)

theorem sum_4_260_4 : blockSum (rowCell 4) 260 4 ≤ (13382986103212086660669 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_260_2 sum_4_262_2 (by norm_num)

theorem sum_4_256_8 : blockSum (rowCell 4) 256 8 ≤ (65720697895616850665571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_256_4 sum_4_260_4 (by norm_num)

theorem sum_4_264_2 : blockSum (rowCell 4) 264 2 ≤ (2006140105435569438263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_264) (by simpa only [blockSum_one] using cell_4_265) (by norm_num)

theorem sum_4_266_2 : blockSum (rowCell 4) 266 2 ≤ (8290819102455923360609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_266) (by simpa only [blockSum_one] using cell_4_267) (by norm_num)

theorem sum_4_264_4 : blockSum (rowCell 4) 264 4 ≤ (4580379907408442637981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_264_2 sum_4_266_2 (by norm_num)

theorem sum_4_268_2 : blockSum (rowCell 4) 268 2 ≤ (6846467469677686064261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_268) (by simpa only [blockSum_one] using cell_4_269) (by norm_num)

theorem sum_4_270_2 : blockSum (rowCell 4) 270 2 ≤ (2824320346273393823883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_270) (by simpa only [blockSum_one] using cell_4_271) (by norm_num)

theorem sum_4_268_4 : blockSum (rowCell 4) 268 4 ≤ (12495108162224473712027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_268_2 sum_4_270_2 (by norm_num)

theorem sum_4_264_8 : blockSum (rowCell 4) 264 8 ≤ (30816627791858244263951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_264_4 sum_4_268_4 (by norm_num)

theorem sum_4_256_16 : blockSum (rowCell 4) 256 16 ≤ (48268662843737547464761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_256_8 sum_4_264_8 (by norm_num)

theorem sum_4_272_2 : blockSum (rowCell 4) 272 2 ≤ (4656235144603010664019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_272) (by simpa only [blockSum_one] using cell_4_273) (by norm_num)

theorem sum_4_274_2 : blockSum (rowCell 4) 274 2 ≤ (3834816424553534978369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_274) (by simpa only [blockSum_one] using cell_4_275) (by norm_num)

theorem sum_4_272_4 : blockSum (rowCell 4) 272 4 ≤ (2122762892289136410597 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_272_2 sum_4_274_2 (by norm_num)

theorem sum_4_276_2 : blockSum (rowCell 4) 276 2 ≤ (1577785836367589525481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_276) (by simpa only [blockSum_one] using cell_4_277) (by norm_num)

theorem sum_4_278_2 : blockSum (rowCell 4) 278 2 ≤ (2594420100498185603217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_278) (by simpa only [blockSum_one] using cell_4_279) (by norm_num)

theorem sum_4_276_4 : blockSum (rowCell 4) 276 4 ≤ (5749991773233364654179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_276_2 sum_4_278_2 (by norm_num)

theorem sum_4_272_8 : blockSum (rowCell 4) 272 8 ≤ (14241043342389910296567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_272_4 sum_4_276_4 (by norm_num)

theorem sum_4_280_2 : blockSum (rowCell 4) 280 2 ≤ (1065629503874215812309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_280) (by simpa only [blockSum_one] using cell_4_281) (by norm_num)

theorem sum_4_282_2 : blockSum (rowCell 4) 282 2 ≤ (1749325615608619785439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_282) (by simpa only [blockSum_one] using cell_4_283) (by norm_num)

theorem sum_4_280_4 : blockSum (rowCell 4) 280 4 ≤ (3880584623357051410057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_280_2 sum_4_282_2 (by norm_num)

theorem sum_4_284_2 : blockSum (rowCell 4) 284 2 ≤ (28693154432112082489 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_284) (by simpa only [blockSum_one] using cell_4_285) (by norm_num)

theorem sum_4_286_2 : blockSum (rowCell 4) 286 2 ≤ (235127706412892321929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_286) (by simpa only [blockSum_one] using cell_4_287) (by norm_num)

theorem sum_4_284_4 : blockSum (rowCell 4) 284 4 ≤ (522059250734013146819 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_284_2 sum_4_286_2 (by norm_num)

theorem sum_4_280_8 : blockSum (rowCell 4) 280 8 ≤ (811360109628389643019 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_280_4 sum_4_284_4 (by norm_num)

theorem sum_4_272_16 : blockSum (rowCell 4) 272 16 ≤ (20731924219417027440719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_272_8 sum_4_280_8 (by norm_num)

theorem sum_4_256_32 : blockSum (rowCell 4) 256 32 ≤ (117269249906892122370241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_256_16 sum_4_272_16 (by norm_num)

#print axioms sum_4_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
