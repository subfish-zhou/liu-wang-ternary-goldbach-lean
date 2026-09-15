import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_256_0 : expNegUpper (225502680079593723323 / 2751452225898774000 : ℝ) ≤ (1275351067927437312109793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_256_1 : expNegUpper (11559971752580429769473 / 140874353966017228800 : ℝ) ≤ (2305562073252017591898507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_256 : rowCell 1 256 ≤ (354123149177949949872807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1275351067927437312109793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2305562073252017591898507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_256_1
  · norm_num [gridPoint]

theorem exp_1_257_0 : expNegUpper (34841339219521138200859 / 424590237044379750400 : ℝ) ≤ (461112359095083022093307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_257_1 : expNegUpper (87210824283487349831943 / 1061475592610949376000 : ℝ) ≤ (2083548919141499340042027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1900039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_257 : rowCell 1 257 ≤ (320057896651523065365161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (461112359095083022093307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2083548919141499340042027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_257_1
  · norm_num [gridPoint]

theorem exp_1_258_0 : expNegUpper (87615820335117288147447 / 1066404949629647104000 : ℝ) ≤ (2083548670431301548247259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1900039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_258_1 : expNegUpper (175448030952173675493733 / 2132809899259294208000 : ℝ) ≤ (470631594692132894827883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950773 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_258 : rowCell 1 258 ≤ (289209755858203847136663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2083548670431301548247259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (470631594692132894827883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_258_1
  · norm_num [gridPoint]

theorem exp_1_259_0 : expNegUpper (2350145360151377094839 / 28569219354699264000 : ℝ) ≤ (941263078062179334930627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950773 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_259_1 : expNegUpper (588262444788806735869 / 7142304838674816000 : ℝ) ≤ (850275272816961445715917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_259 : rowCell 1 259 ≤ (261281172262688127405583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (941263078062179334930627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (850275272816961445715917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_259_1
  · norm_num [gridPoint]

theorem exp_1_260_0 : expNegUpper (44323622528325113796863 / 538148960562837632000 : ℝ) ≤ (1700550346360464190137909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1903057 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_260_1 : expNegUpper (177513766012718382193851 / 2152595842251350528000 : ℝ) ≤ (307170662643027907970839 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476143 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_260 : rowCell 1 260 ≤ (236001462562665923947501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1700550346360464190137909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (307170662643027907970839 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_260_1
  · norm_num [gridPoint]

theorem exp_1_261_0 : expNegUpper (178332414968414742247539 / 2162523071206011392000 : ℝ) ≤ (1535853134891655649968487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476143 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_261_1 : expNegUpper (714212554690965626089 / 8650092284824045568 : ℝ) ≤ (693413454829456262765123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_261 : rowCell 1 261 ≤ (213124454693979957258463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1535853134891655649968487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (693413454829456262765123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_261_1
  · norm_num [gridPoint]

theorem exp_1_262_0 : expNegUpper (239166248758713053363 / 2896630851288569856 : ℝ) ≤ (1386826750111728492016041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1906091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_262_1 : expNegUpper (59865620469683246824987 / 724157712822142464000 : ℝ) ≤ (250401949793674479518923 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381523 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_262 : rowCell 1 262 ≤ (192426328342588099148553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1386826750111728492016041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (250401949793674479518923 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_262_1
  · norm_num [gridPoint]

theorem exp_1_263_0 : expNegUpper (180421314907499245240649 / 2182446044032598528000 : ℝ) ≤ (156501200780759365906547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381523 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_263_1 : expNegUpper (22580618026747753847631 / 272805755504074816000 : ℝ) ≤ (565036745518285171032261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_263 : rowCell 1 263 ≤ (86851819803316603957599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156501200780759365906547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (565036745518285171032261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_263_1
  · norm_num [gridPoint]

theorem exp_1_264_0 : expNegUpper (907361549880733773159 / 10962208939522624000 : ℝ) ≤ (226014672677529790254169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_264_1 : expNegUpper (7267895883195076966783 / 87697671516180992000 : ℝ) ≤ (40792448449644417212877 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (76427 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_264 : rowCell 1 264 ≤ (19596439339856456516469 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (226014672677529790254169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40792448449644417212877 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_264_1
  · norm_num [gridPoint]

theorem exp_1_265_0 : expNegUpper (4680196968392717049353 / 56473342822620672000 : ℝ) ≤ (1019811097093806793710167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (76427 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_265_1 : expNegUpper (2343002948706064966277 / 28236671411310336000 : ℝ) ≤ (920126588071150212256547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1912211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_265 : rowCell 1 265 ≤ (141461998914992680266153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1019811097093806793710167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (920126588071150212256547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_265_1
  · norm_num [gridPoint]

theorem exp_1_266_0 : expNegUpper (91793720136672761424307 / 1106250895282821376000 : ℝ) ≤ (57507905375956385356089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1912211 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_266_1 : expNegUpper (36763090592781821422041 / 442500358113128550400 : ℝ) ≤ (207506006111979469984449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_266 : rowCell 1 266 ≤ (6381127381191362501349 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57507905375956385356089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (207506006111979469984449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_266_1
  · norm_num [gridPoint]

theorem exp_1_267_0 : expNegUpper (1191300616042413387951 / 14339135802289254400 : ℝ) ≤ (830023933218604684669437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_267_1 : expNegUpper (1490976419086481371939 / 17923919752861568000 : ℝ) ≤ (93574953132582883775743 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383059 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_267 : rowCell 1 267 ≤ (115114648164327346215137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (830023933218604684669437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93574953132582883775743 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_267_1
  · norm_num [gridPoint]

theorem exp_1_268_0 : expNegUpper (15476679783278355708767 / 186054428870815104000 : ℝ) ≤ (748599543523476850572967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383059 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_268_1 : expNegUpper (61983702999951821043121 / 744217715483260416000 : ℝ) ≤ (675032958207025385199489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479211 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_268 : rowCell 1 268 ≤ (10381256107101399653063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (748599543523476850572967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (675032958207025385199489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_268_1
  · norm_num [gridPoint]

theorem exp_1_269_0 : expNegUpper (7471725440159309987843 / 89710523274019328000 : ℝ) ≤ (675032885344810273791519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479211 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_269_1 : expNegUpper (3740511241112861457321 / 44855261637009664000 : ℝ) ≤ (608579536333569148085473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479599 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_269 : rowCell 1 269 ≤ (93602171034322529112283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (675032885344810273791519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (608579536333569148085473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_269_1
  · norm_num [gridPoint]

theorem exp_1_270_0 : expNegUpper (93935270646420082717041 / 1126447927778470144000 : ℝ) ≤ (608579471234484758858013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (479599 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_270_1 : expNegUpper (188104445126425166059561 / 2252895855556940288000 : ℝ) ≤ (274281977375076120953847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1919953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_270 : rowCell 1 270 ≤ (84379938243846513168141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (608579471234484758858013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (274281977375076120953847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_270_1
  · norm_num [gridPoint]

theorem exp_1_271_0 : expNegUpper (62984127752750387482763 / 754350489189717504000 : ℝ) ≤ (274281948298465890555341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1919953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_271_1 : expNegUpper (788282367518918289329 / 9429381114871468800 : ℝ) ≤ (61796704108808384237177 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (960757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_271 : rowCell 1 271 ≤ (1521038833258987107467 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (274281948298465890555341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61796704108808384237177 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_271_1
  · norm_num [gridPoint]

theorem exp_1_272_0 : expNegUpper (2375483398656929843347 / 28415373973588998400 : ℝ) ≤ (494373580930752815590879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (960757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_272_1 : expNegUpper (190275541282327389733311 / 2273229917887119872000 : ℝ) ≤ (44545310683832789403271 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_272 : rowCell 1 272 ≤ (68533006447661157879203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (494373580930752815590879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44545310683832789403271 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_272_1
  · norm_num [gridPoint]

theorem exp_1_273_0 : expNegUpper (191129417188088487221559 / 2283431206510842368000 : ℝ) ≤ (22272653022798900306019 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1923079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_273_1 : expNegUpper (95683887176062406835839 / 1141715603255421184000 : ℝ) ≤ (401298826561195603962653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_273 : rowCell 1 273 ≤ (61745908354940791639171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22272653022798900306019 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (401298826561195603962653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_273_1
  · norm_num [gridPoint]

theorem exp_1_274_0 : expNegUpper (51259901103251228917 / 611641422250752000 : ℝ) ≤ (401298785148466516611609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1924647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_274_1 : expNegUpper (102647721283344697591 / 1223282844501504000 : ℝ) ≤ (72290882802704581853911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (96311 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_274 : rowCell 1 274 ≤ (5562064856896964103513 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (401298785148466516611609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (72290882802704581853911 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_274_1
  · norm_num [gridPoint]

theorem exp_1_275_0 : expNegUpper (193324317732203897848397 / 2303902298675552768000 : ℝ) ≤ (361454377044040665810499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (96311 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_275_1 : expNegUpper (48391415109276379849179 / 575975574668888192000 : ℝ) ≤ (162753171607860654428703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_275 : rowCell 1 275 ≤ (50093792912613951572683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (361454377044040665810499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (162753171607860654428703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_275_1
  · norm_num [gridPoint]

theorem exp_1_276_0 : expNegUpper (48607123241365625544891 / 578543025554135168000 : ℝ) ≤ (5086036097158808077263 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1927797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_276_1 : expNegUpper (38934266687393218928303 / 462834420443308134400 : ℝ) ≤ (73270001390346086970239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_276 : rowCell 1 276 ≤ (45107869907787728074811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5086036097158808077263 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73270001390346086970239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_276_1
  · norm_num [gridPoint]

theorem exp_1_277_0 : expNegUpper (13035810988620437877421 / 154964316270885580800 : ℝ) ≤ (293079976113803335362157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1929379 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_277_1 : expNegUpper (32630251066365280074431 / 387410790677213952000 : ℝ) ≤ (131918063587973453527097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482741 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_277 : rowCell 1 277 ≤ (1269088206443754283187 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (293079976113803335362157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (131918063587973453527097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_277_1
  · norm_num [gridPoint]

theorem exp_1_278_0 : expNegUpper (7563474742925951635489 / 89799239392914688000 : ℝ) ≤ (52767220180133471034797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (482741 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_278_1 : expNegUpper (15145860716393917195461 / 179598478785829376000 : ℝ) ≤ (118733753881500236881401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_278 : rowCell 1 278 ≤ (4569438691714445856267 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52767220180133471034797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118733753881500236881401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_278_1
  · norm_num [gridPoint]

theorem exp_1_279_0 : expNegUpper (7910721536724226879713 / 93804741706961408000 : ℝ) ≤ (237467484322038016125543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1932553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_279_1 : expNegUpper (990076960870462353269 / 11725592713370176000 : ℝ) ≤ (106848026473778710846053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (967073 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_279 : rowCell 1 279 ≤ (6579850095987882995563 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (237467484322038016125543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (106848026473778710846053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_279_1
  · norm_num [gridPoint]

theorem exp_1_280_0 : expNegUpper (8287094171989083470863 / 98144987476585152000 : ℝ) ≤ (26712004004812915131239 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (967073 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_280_1 : expNegUpper (66379708324481656171357 / 785159899812681216000 : ℝ) ≤ (96135037237513070182947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1935743 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_280 : rowCell 1 280 ≤ (29603413222140389075567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26712004004812915131239 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96135037237513070182947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_280_1
  · norm_num [gridPoint]

theorem exp_1_281_0 : expNegUpper (200017018437310383175439 / 2365863694507807232000 : ℝ) ≤ (96135027913676220832079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1935743 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_281_1 : expNegUpper (20026739770351706385087 / 236586369450780723200 : ℝ) ≤ (34592366957155523944673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (30271 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_281 : rowCell 1 281 ≤ (13316518800768083405209 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96135027913676220832079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34592366957155523944673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_281_1
  · norm_num [gridPoint]

theorem exp_1_282_0 : expNegUpper (20114832333916145834607 / 237627052788332595200 : ℝ) ≤ (86480909078760188429757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (30271 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_282_1 : expNegUpper (201400220356647403393261 / 2376270527883325952000 : ℝ) ≤ (31113062894432511265023 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1938949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_282 : rowCell 1 282 ≤ (2994561709056525183573 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86480909078760188429757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31113062894432511265023 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_282_1
  · norm_num [gridPoint]

theorem exp_1_283_0 : expNegUpper (67428061608543291847223 / 795566733188199936000 : ℝ) ≤ (155565299646945087219341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1938949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_283_1 : expNegUpper (16878133577097886155859 / 198891683297049984000 : ℝ) ≤ (69947091475451534236453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_283 : rowCell 1 283 ≤ (10772585461456992008641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (155565299646945087219341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69947091475451534236453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_283_1
  · norm_num [gridPoint]

theorem exp_1_284_0 : expNegUpper (2034246128890542814913 / 23971527095516288000 : ℝ) ≤ (27978833947052989932169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (970279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_284_1 : expNegUpper (8147182216057496080443 / 95886108382065152000 : ℝ) ≤ (12577995436123764813863 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1942171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_284 : rowCell 1 284 ≤ (19373195820712837383091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27978833947052989932169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12577995436123764813863 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_284_1
  · norm_num [gridPoint]

theorem exp_1_285_0 : expNegUpper (204569617521773322924027 / 2407628057844412928000 : ℝ) ≤ (3144498564555963844441 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1942171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_285_1 : expNegUpper (102413043888887177272313 / 1203814028922206464000 : ℝ) ≤ (22614062447895496223727 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485947 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_285 : rowCell 1 285 ≤ (17417175173625349650137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3144498564555963844441 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22614062447895496223727 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_285_1
  · norm_num [gridPoint]

theorem exp_1_286_0 : expNegUpper (34286534786020941094819 / 403021040740492032000 : ℝ) ≤ (28267575435637009057817 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485947 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_286_1 : expNegUpper (2746362800620321842667 / 32241683259239362560 : ℝ) ≤ (4065103517374337877531 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_286 : rowCell 1 286 ≤ (1956995375984409668549 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28267575435637009057817 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4065103517374337877531 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_286_1
  · norm_num [gridPoint]

theorem exp_1_287_0 : expNegUpper (8274935858577995966201 / 97145890773889863680 : ℝ) ≤ (6351723661335814497283 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_287_1 : expNegUpper (6472904131250793740823 / 75895227167101456000 : ℝ) ≤ (91327379024605168985209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_287 : rowCell 1 287 ≤ (879403054162353408357 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6351723661335814497283 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (91327379024605168985209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_287_1
  · norm_num [gridPoint]

theorem sum_1_256_2 : blockSum (rowCell 1) 256 2 ≤ (42136315364342063452373 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_256) (by simpa only [blockSum_one] using cell_1_257) (by norm_num)

theorem sum_1_258_2 : blockSum (rowCell 1) 258 2 ≤ (275245464060445987271123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_258) (by simpa only [blockSum_one] using cell_1_259) (by norm_num)

theorem sum_1_256_4 : blockSum (rowCell 1) 256 4 ≤ (612335986975182494890107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_256_2 sum_1_258_2 (by norm_num)

theorem sum_1_260_2 : blockSum (rowCell 1) 260 2 ≤ (112281479314161470301491 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_260) (by simpa only [blockSum_one] using cell_1_261) (by norm_num)

theorem sum_1_262_2 : blockSum (rowCell 1) 262 2 ≤ (366129967949221307063751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_262) (by simpa only [blockSum_one] using cell_1_263) (by norm_num)

theorem sum_1_260_4 : blockSum (rowCell 1) 260 4 ≤ (163051177041173437653943 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_260_2 sum_1_262_2 (by norm_num)

theorem sum_1_256_8 : blockSum (rowCell 1) 256 8 ≤ (2039927859156232178049929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_256_4 sum_1_260_4 (by norm_num)

theorem sum_1_264_2 : blockSum (rowCell 1) 264 2 ≤ (59646702726768866479581 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_264) (by simpa only [blockSum_one] using cell_1_265) (by norm_num)

theorem sum_1_266_2 : blockSum (rowCell 1) 266 2 ≤ (242737195788154596242117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_266) (by simpa only [blockSum_one] using cell_1_267) (by norm_num)

theorem sum_1_264_4 : blockSum (rowCell 1) 264 4 ≤ (270485354710999464320011 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_264_2 sum_1_266_2 (by norm_num)

theorem sum_1_268_2 : blockSum (rowCell 1) 268 2 ≤ (197414732105336525642913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_268) (by simpa only [blockSum_one] using cell_1_269) (by norm_num)

theorem sum_1_270_2 : blockSum (rowCell 1) 270 2 ≤ (160431879906795868541491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_270) (by simpa only [blockSum_one] using cell_1_271) (by norm_num)

theorem sum_1_268_4 : blockSum (rowCell 1) 268 4 ≤ (89461653003033098546101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_268_2 sum_1_270_2 (by norm_num)

theorem sum_1_264_8 : blockSum (rowCell 1) 264 8 ≤ (449408660717065661412213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_264_4 sum_1_268_4 (by norm_num)

theorem sum_1_256_16 : blockSum (rowCell 1) 256 16 ≤ (587749036118072700174871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_256_8 sum_1_264_8 (by norm_num)

theorem sum_1_272_2 : blockSum (rowCell 1) 272 2 ≤ (65139457401300974759187 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_272) (by simpa only [blockSum_one] using cell_1_273) (by norm_num)

theorem sum_1_274_2 : blockSum (rowCell 1) 274 2 ≤ (105714441481583592607813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_274) (by simpa only [blockSum_one] using cell_1_275) (by norm_num)

theorem sum_1_272_4 : blockSum (rowCell 1) 272 4 ≤ (235993356284185542126187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_272_2 sum_1_274_2 (by norm_num)

theorem sum_1_276_2 : blockSum (rowCell 1) 276 2 ≤ (17143738502797573027359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_276) (by simpa only [blockSum_one] using cell_1_277) (by norm_num)

theorem sum_1_278_2 : blockSum (rowCell 1) 278 2 ≤ (69454760013654981827951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_278) (by simpa only [blockSum_one] using cell_1_279) (by norm_num)

theorem sum_1_276_4 : blockSum (rowCell 1) 276 4 ≤ (77586726263821423482373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_276_2 sum_1_278_2 (by norm_num)

theorem sum_1_272_8 : blockSum (rowCell 1) 272 8 ≤ (391166808811828389090933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_272_4 sum_1_276_4 (by norm_num)

theorem sum_1_280_2 : blockSum (rowCell 1) 280 2 ≤ (11247290164735311177197 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_280) (by simpa only [blockSum_one] using cell_1_281) (by norm_num)

theorem sum_1_282_2 : blockSum (rowCell 1) 282 2 ≤ (22750832297683092742933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_282) (by simpa only [blockSum_one] using cell_1_283) (by norm_num)

theorem sum_1_280_4 : blockSum (rowCell 1) 280 4 ≤ (101738115419042741371851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_280_2 sum_1_282_2 (by norm_num)

theorem sum_1_284_2 : blockSum (rowCell 1) 284 2 ≤ (9197592748584546758307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_284) (by simpa only [blockSum_one] using cell_1_285) (by norm_num)

theorem sum_1_286_2 : blockSum (rowCell 1) 286 2 ≤ (3715801484309116485263 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_286) (by simpa only [blockSum_one] using cell_1_287) (by norm_num)

theorem sum_1_284_4 : blockSum (rowCell 1) 284 4 ≤ (16629195717202779728833 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_284_2 sum_1_286_2 (by norm_num)

theorem sum_1_280_8 : blockSum (rowCell 1) 280 8 ≤ (168254898287853860287183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_280_4 sum_1_284_4 (by norm_num)

theorem sum_1_272_16 : blockSum (rowCell 1) 272 16 ≤ (139855426774920562344529 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_272_8 sum_1_280_8 (by norm_num)

theorem sum_1_256_32 : blockSum (rowCell 1) 256 32 ≤ (3498166887690045750252471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_256_16 sum_1_272_16 (by norm_num)

#print axioms sum_1_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
