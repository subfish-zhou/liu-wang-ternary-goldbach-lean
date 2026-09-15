import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_256_0 : expNegUpper (711217006976701169969 / 8254356677696322000 : ℝ) ≤ (38061261680583294240589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980197 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_256_1 : expNegUpper (36452888038608054108419 / 422623061898051686400 : ℝ) ≤ (34740856794065744689293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (30653 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_256 : rowCell 6 256 ≤ (5308795887324724986263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38061261680583294240589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34740856794065744689293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_256_1
  · norm_num [gridPoint]

theorem exp_6_257_0 : expNegUpper (36622564632617381400859 / 424590237044379750400 : ℝ) ≤ (868521292405008692371 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (30653 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_257_1 : expNegUpper (91653572025941109831943 / 1061475592610949376000 : ℝ) ≤ (31702099245255126563571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (392639 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_257 : rowCell 6 257 ≤ (2422539838744834823413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (868521292405008692371 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31702099245255126563571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_257_1
  · norm_num [gridPoint]

theorem exp_6_258_0 : expNegUpper (4846273666218144428813 / 56126576296297216000 : ℝ) ≤ (7925523659063247497811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (392639 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_258_1 : expNegUpper (9702850421981836394407 / 112253152592594432000 : ℝ) ≤ (28921878322461453854611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491151 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_258 : rowCell 6 258 ≤ (552594321875020292531 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7925523659063247497811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28921878322461453854611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_258_1
  · norm_num [gridPoint]

theorem exp_6_259_0 : expNegUpper (7408331689519275604517 / 85707658064097792000 : ℝ) ≤ (28921874156399209305019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491151 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_259_1 : expNegUpper (1854054920826969327607 / 21426914516024448000 : ℝ) ≤ (13189450546006887238833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1966017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_259 : rowCell 6 259 ≤ (2016291107702268511737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28921874156399209305019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13189450546006887238833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_259_1
  · norm_num [gridPoint]

theorem exp_6_260_0 : expNegUpper (46565627980125689796863 / 538148960562837632000 : ℝ) ≤ (2637889732718169645739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1966017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_260_1 : expNegUpper (186461156239346990193851 / 2152595842251350528000 : ℝ) ≤ (4810712227909489021263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393487 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_260 : rowCell 6 260 ≤ (3677580181805792704789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2637889732718169645739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4810712227909489021263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_260_1
  · norm_num [gridPoint]

theorem exp_6_261_0 : expNegUpper (187321068356190742247539 / 2162523071206011392000 : ℝ) ≤ (24053557738073243290257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393487 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_261_1 : expNegUpper (750084641919774842089 / 8650092284824045568 : ℝ) ≤ (21927811309185030544839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_261 : rowCell 6 261 ≤ (3353002742312326724161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24053557738073243290257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21927811309185030544839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_261_1
  · norm_num [gridPoint]

theorem exp_6_262_0 : expNegUpper (753535886149537944089 / 8689892553865709568 : ℝ) ≤ (10963904118345081974683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968857 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_262_1 : expNegUpper (188585514796825740474961 / 2172473138466427392000 : ℝ) ≤ (799401818345118027709 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (394057 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_262 : rowCell 6 262 ≤ (305632294754208880707 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10963904118345081974683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (799401818345118027709 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_262_1
  · norm_num [gridPoint]

theorem exp_6_263_0 : expNegUpper (189451231456422637240649 / 2182446044032598528000 : ℝ) ≤ (9992521341956880221877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (394057 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_263_1 : expNegUpper (23706778647791465847631 / 272805755504074816000 : ℝ) ≤ (18209988645317667952579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_263 : rowCell 6 263 ≤ (2785216000376015615023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9992521341956880221877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18209988645317667952579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_263_1
  · norm_num [gridPoint]

theorem exp_6_264_0 : expNegUpper (952614290528219213159 / 10962208939522624000 : ℝ) ≤ (18209986140078839215621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971717 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_264_1 : expNegUpper (7629092545152012646783 / 87697671516180992000 : ℝ) ≤ (16588595191831014526511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (986577 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_264 : rowCell 6 264 ≤ (634385953768320480659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18209986140078839215621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16588595191831014526511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_264_1
  · norm_num [gridPoint]

theorem exp_6_265_0 : expNegUpper (191598861477386748924767 / 2202460370082206208000 : ℝ) ≤ (16588592930394076199901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (986577 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_265_1 : expNegUpper (95902389064285077684803 / 1101230185041103104000 : ℝ) ≤ (3021590822055030779181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (493649 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_265 : rowCell 6 265 ≤ (288917585946510263731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16588592930394076199901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3021590822055030779181 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_265_1
  · norm_num [gridPoint]

theorem exp_6_266_0 : expNegUpper (96339625781995001424307 / 1106250895282821376000 : ℝ) ≤ (15107952069359907922429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (493649 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_266_1 : expNegUpper (38577326534795978222041 / 442500358113128550400 : ℝ) ≤ (3439050348914547125383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_266 : rowCell 6 266 ≤ (65775000103343697451 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15107952069359907922429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3439050348914547125383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_266_1
  · norm_num [gridPoint]

theorem exp_6_267_0 : expNegUpper (1250090570050272587951 / 14339135802289254400 : ℝ) ≤ (13756199554160130134447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_267_1 : expNegUpper (1564297477882001371939 / 17923919752861568000 : ℝ) ≤ (2504487745410304093989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988747 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_267 : rowCell 6 267 ≤ (383252382636006867633 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13756199554160130134447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2504487745410304093989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_267_1
  · norm_num [gridPoint]

theorem exp_6_268_0 : expNegUpper (48713307962783035126301 / 558163286612445312000 : ℝ) ≤ (3130609266460866871201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988747 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_268_1 : expNegUpper (195063551871073639129363 / 2232653146449781248000 : ℝ) ≤ (5698329071427177830671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1978949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_268 : rowCell 6 268 ≤ (436050478107586707067 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3130609266460866871201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5698329071427177830671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_268_1
  · norm_num [gridPoint]

theorem exp_6_269_0 : expNegUpper (7837873681453932707843 / 89710523274019328000 : ℝ) ≤ (11396656644605649226503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1978949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_269_1 : expNegUpper (3923172730148698897321 / 44855261637009664000 : ℝ) ≤ (5184836141323892411267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (198041 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_269 : rowCell 6 269 ≤ (1587220261061465990113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11396656644605649226503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5184836141323892411267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_269_1
  · norm_num [gridPoint]

theorem exp_6_270_0 : expNegUpper (98522439452889714717041 / 1126447927778470144000 : ℝ) ≤ (5184835465829779182943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (198041 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_270_1 : expNegUpper (197258151158790734059561 / 2252895855556940288000 : ℝ) ≤ (9433049813017574935907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (3171 / 1600 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_270 : rowCell 6 270 ≤ (1444032188208775606229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5184835465829779182943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9433049813017574935907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_270_1
  · norm_num [gridPoint]

theorem exp_6_271_0 : expNegUpper (198147352451764122448289 / 2263051467569152512000 : ℝ) ≤ (1179131074384088832357 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (3171 / 1600 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_271_1 : expNegUpper (2479526322718495667987 / 28288143344614406400 : ℝ) ≤ (1072381959795725146359 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (396669 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_271 : rowCell 6 271 ≤ (1313458826369069450037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1179131074384088832357 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1072381959795725146359 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_271_1
  · norm_num [gridPoint]

theorem exp_6_272_0 : expNegUpper (2490678408333013043347 / 28415373973588998400 : ℝ) ≤ (4289527290296153799807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (396669 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_272_1 : expNegUpper (199470510475840349733311 / 2273229917887119872000 : ℝ) ≤ (7800595840158610614299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (99241 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_272 : rowCell 6 272 ≤ (597209412386665924781 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4289527290296153799807 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7800595840158610614299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_272_1
  · norm_num [gridPoint]

theorem exp_6_273_0 : expNegUpper (200365649542748839221559 / 2283431206510842368000 : ℝ) ≤ (1560118970181051886481 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (99241 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_273_1 : expNegUpper (100291687563105734835839 / 1141715603255421184000 : ℝ) ≤ (3545583094654674838627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_273 : rowCell 6 273 ≤ (108592059436900886409 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1560118970181051886481 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3545583094654674838627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_273_1
  · norm_num [gridPoint]

theorem exp_6_274_0 : expNegUpper (161185194457940925151 / 1834924266752256000 : ℝ) ≤ (709116529803250669831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986299 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_274_1 : expNegUpper (322721135617490655973 / 3669848533504512000 : ℝ) ≤ (3222402668256475412727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (993891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_274 : rowCell 6 274 ≤ (246763784973667934267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (709116529803250669831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3222402668256475412727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_274_1
  · norm_num [gridPoint]

theorem exp_6_275_0 : expNegUpper (202601813248011641848397 / 2303902298675552768000 : ℝ) ≤ (1611201133418406235773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (993891 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_275_1 : expNegUpper (50705631093084891849179 / 575975574668888192000 : ℝ) ≤ (5856051004369750715281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1989271 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_275 : rowCell 6 275 ≤ (448494718692010206927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1611201133418406235773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5856051004369750715281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_275_1
  · norm_num [gridPoint]

theorem exp_6_276_0 : expNegUpper (50931655015460985544891 / 578543025554135168000 : ℝ) ≤ (73200628516749582177 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1989271 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_276_1 : expNegUpper (40789765790554767728303 / 462834420443308134400 : ℝ) ≤ (531989976310629848069 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_276 : rowCell 6 276 ≤ (814960318133639704991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (73200628516749582177 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (531989976310629848069 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_276_1
  · norm_num [gridPoint]

theorem exp_6_277_0 : expNegUpper (2156378142171175833277 / 24468049937508249600 : ℝ) ≤ (5319899112083973971717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_277_1 : expNegUpper (5396832460383503169647 / 61170124843770624000 : ℝ) ≤ (966353973731802968737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1992261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_277 : rowCell 6 277 ≤ (740268822715878630699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5319899112083973971717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (966353973731802968737 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_277_1
  · norm_num [gridPoint]

theorem exp_6_278_0 : expNegUpper (102994866786801787261357 / 1167390112107890944000 : ℝ) ≤ (4831769282590593830567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1992261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_278_1 : expNegUpper (206214947990076059540993 / 2334780224215781888000 : ℝ) ≤ (4387466977875627423583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_278 : rowCell 6 278 ≤ (336137495510387308237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4831769282590593830567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4387466977875627423583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_278_1
  · norm_num [gridPoint]

theorem exp_6_279_0 : expNegUpper (8285122410248327999713 / 93804741706961408000 : ℝ) ≤ (4387466450385781812637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1993763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_279_1 : expNegUpper (1036773912158106513269 / 11725592713370176000 : ℝ) ≤ (3983152530650792679839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_279 : rowCell 6 279 ≤ (610393056575177787039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4387466450385781812637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3983152530650792679839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_279_1
  · norm_num [gridPoint]

theorem exp_6_280_0 : expNegUpper (26033864193301778412589 / 294434962429755456000 : ℝ) ≤ (79663041119571329527 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_280_1 : expNegUpper (208499146811547496514071 / 2355479699438043648000 : ℝ) ≤ (1807657301493742777917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (99839 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_280 : rowCell 6 280 ≤ (554087015519193429 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79663041119571329527 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1807657301493742777917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_280_1
  · norm_num [gridPoint]

theorem exp_6_281_0 : expNegUpper (209418303436560303175439 / 2365863694507807232000 : ℝ) ≤ (903828543982076826011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (99839 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_281_1 : expNegUpper (20964805112219328785087 / 236586369450780723200 : ℝ) ≤ (3280741048305291971137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_281 : rowCell 6 281 ≤ (502866542625729581521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (903828543982076826011 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3280741048305291971137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_281_1
  · norm_num [gridPoint]

theorem exp_6_282_0 : expNegUpper (21057023991898507434607 / 237627052788332595200 : ℝ) ≤ (3280740664158331319121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_282_1 : expNegUpper (210801505355897323393261 / 2376270527883325952000 : ℝ) ≤ (2976494756840657485661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249977 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_282 : rowCell 6 282 ≤ (28517701789637176089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3280740664158331319121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2976494756840657485661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_282_1
  · norm_num [gridPoint]

theorem exp_6_283_0 : expNegUpper (211726732986027187541669 / 2386700199564599808000 : ℝ) ≤ (1488247205680523446383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249977 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_283_1 : expNegUpper (52989879876249562467577 / 596675049891149952000 : ℝ) ≤ (539978174948312824891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100067 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_283 : rowCell 6 283 ≤ (413927114940007878191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1488247205680523446383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (539978174948312824891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_283_1
  · norm_num [gridPoint]

theorem exp_6_284_0 : expNegUpper (2128877926300252894913 / 23971527095516288000 : ℝ) ≤ (2699890564097048255059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100067 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_284_1 : expNegUpper (8524884142473388560443 / 95886108382065152000 : ℝ) ≤ (2448475835488212371087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2002869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_284 : rowCell 6 284 ≤ (187711751671597166121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2699890564097048255059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2448475835488212371087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_284_1
  · norm_num [gridPoint]

theorem exp_6_285_0 : expNegUpper (214053428843318026924027 / 2407628057844412928000 : ℝ) ≤ (1224237778109912894269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2002869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_285_1 : expNegUpper (107144633759372681272313 / 1203814028922206464000 : ℝ) ≤ (1110004033304612277881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1002201 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_285 : rowCell 6 285 ≤ (170215010058724618291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1224237778109912894269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1110004033304612277881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_285_1
  · norm_num [gridPoint]

theorem exp_6_286_0 : expNegUpper (107611825809122023284457 / 1209063122221476096000 : ℝ) ≤ (1110003907797816608731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1002201 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_286_1 : expNegUpper (8618440854722753688001 / 96725049777718087680 : ℝ) ≤ (62888757635803080001 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100297 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_286 : rowCell 6 286 ≤ (77158478780243941689 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1110003907797816608731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62888757635803080001 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_286_1
  · norm_num [gridPoint]

theorem exp_6_287_0 : expNegUpper (8655938837885679806201 / 97145890773889863680 : ℝ) ≤ (402488003754174514307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (100297 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_287_1 : expNegUpper (6769917971941993740823 / 75895227167101456000 : ℝ) ≤ (1823902977978002323353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1003741 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_287 : rowCell 6 287 ≤ (279749578037339098903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (402488003754174514307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1823902977978002323353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_287_1
  · norm_num [gridPoint]

theorem sum_6_256_2 : blockSum (rowCell 6) 256 2 ≤ (10153875564814394633089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_256) (by simpa only [blockSum_one] using cell_6_257) (by norm_num)

theorem sum_6_258_2 : blockSum (rowCell 6) 258 2 ≤ (4226668395202349681861 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_258) (by simpa only [blockSum_one] using cell_6_259) (by norm_num)

theorem sum_6_256_4 : blockSum (rowCell 6) 256 4 ≤ (18607212355219093996811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_256_2 sum_6_258_2 (by norm_num)

theorem sum_6_260_2 : blockSum (rowCell 6) 260 2 ≤ (140611658482362388579 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_260) (by simpa only [blockSum_one] using cell_6_261) (by norm_num)

theorem sum_6_262_2 : blockSum (rowCell 6) 262 2 ≤ (5841538947918104422093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_262) (by simpa only [blockSum_one] using cell_6_263) (by norm_num)

theorem sum_6_260_4 : blockSum (rowCell 6) 260 4 ≤ (12872121872036223851043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_260_2 sum_6_262_2 (by norm_num)

theorem sum_6_256_8 : blockSum (rowCell 6) 256 8 ≤ (15739667113627658923927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_256_4 sum_6_260_4 (by norm_num)

theorem sum_6_264_2 : blockSum (rowCell 6) 264 2 ≤ (1212221125661341008121 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_264) (by simpa only [blockSum_one] using cell_6_265) (by norm_num)

theorem sum_6_266_2 : blockSum (rowCell 6) 266 2 ≤ (4021061916487032656597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_266) (by simpa only [blockSum_one] using cell_6_267) (by norm_num)

theorem sum_6_264_4 : blockSum (rowCell 6) 264 4 ≤ (8869946419132396689081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_264_2 sum_6_266_2 (by norm_num)

theorem sum_6_268_2 : blockSum (rowCell 6) 268 2 ≤ (3331422173491812818381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_268) (by simpa only [blockSum_one] using cell_6_269) (by norm_num)

theorem sum_6_270_2 : blockSum (rowCell 6) 270 2 ≤ (1378745507288922528133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_270) (by simpa only [blockSum_one] using cell_6_271) (by norm_num)

theorem sum_6_268_4 : blockSum (rowCell 6) 268 4 ≤ (6088913188069657874647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_268_2 sum_6_270_2 (by norm_num)

theorem sum_6_264_8 : blockSum (rowCell 6) 264 8 ≤ (934928725450128410233 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_264_4 sum_6_268_4 (by norm_num)

theorem sum_6_256_16 : blockSum (rowCell 6) 256 16 ≤ (23219096917228686205791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_256_8 sum_6_264_8 (by norm_num)

theorem sum_6_272_2 : blockSum (rowCell 6) 272 2 ≤ (570084854785585178413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_272) (by simpa only [blockSum_one] using cell_6_273) (by norm_num)

theorem sum_6_274_2 : blockSum (rowCell 6) 274 2 ≤ (942022288639346075461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_274) (by simpa only [blockSum_one] using cell_6_275) (by norm_num)

theorem sum_6_272_4 : blockSum (rowCell 6) 272 4 ≤ (2082191998210516432287 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_272_2 sum_6_274_2 (by norm_num)

theorem sum_6_276_2 : blockSum (rowCell 6) 276 2 ≤ (155522914084951833569 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_276) (by simpa only [blockSum_one] using cell_6_277) (by norm_num)

theorem sum_6_278_2 : blockSum (rowCell 6) 278 2 ≤ (1282668047595952403513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_278) (by simpa only [blockSum_one] using cell_6_279) (by norm_num)

theorem sum_6_276_4 : blockSum (rowCell 6) 276 4 ≤ (2837897188445470739203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_276_2 sum_6_278_2 (by norm_num)

theorem sum_6_272_8 : blockSum (rowCell 6) 272 8 ≤ (7002281184866503603777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_272_4 sum_6_276_4 (by norm_num)

theorem sum_6_280_2 : blockSum (rowCell 6) 280 2 ≤ (1056953558144923010521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_280) (by simpa only [blockSum_one] using cell_6_281) (by norm_num)

theorem sum_6_282_2 : blockSum (rowCell 6) 282 2 ≤ (174042068714840539123 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_282) (by simpa only [blockSum_one] using cell_6_283) (by norm_num)

theorem sum_6_280_4 : blockSum (rowCell 6) 280 4 ≤ (240895487714890713267 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_280_2 sum_6_282_2 (by norm_num)

theorem sum_6_284_2 : blockSum (rowCell 6) 284 2 ≤ (89481690432580446103 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_284) (by simpa only [blockSum_one] using cell_6_285) (by norm_num)

theorem sum_6_286_2 : blockSum (rowCell 6) 286 2 ≤ (588383493158314865659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_286) (by simpa only [blockSum_one] using cell_6_287) (by norm_num)

theorem sum_6_284_4 : blockSum (rowCell 6) 284 4 ≤ (1304237016618958434483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_284_2 sum_6_286_2 (by norm_num)

theorem sum_6_280_8 : blockSum (rowCell 6) 280 8 ≤ (3231400918338084140619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_280_4 sum_6_284_4 (by norm_num)

theorem sum_6_272_16 : blockSum (rowCell 6) 272 16 ≤ (2558420525801146936099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_272_8 sum_6_280_8 (by norm_num)

theorem sum_6_256_32 : blockSum (rowCell 6) 256 32 ≤ (28335937968830980077989 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_256_16 sum_6_272_16 (by norm_num)

#print axioms sum_6_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
