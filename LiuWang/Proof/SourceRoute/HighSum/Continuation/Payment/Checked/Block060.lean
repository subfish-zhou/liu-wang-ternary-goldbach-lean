import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_384_0 : expNegUpper (109493923703365297689 / 1111792860099364000 : ℝ) ≤ (21195377274580151 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1079243 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_384_1 : expNegUpper (14031607864602801206503 / 142309486092718592000 : ℝ) ≤ (37780362907517287 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540107 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_384 : rowCell 3 384 ≤ (584614991367927 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21195377274580151 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37780362907517287 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_384_1
  · norm_num [gridPoint]

theorem exp_3_385_0 : expNegUpper (39116471354639753346703 / 396721814576251392000 : ℝ) ≤ (75560722105463981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (540107 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_385_1 : expNegUpper (19581096876535092208207 / 198360907288125696000 : ℝ) ≤ (67335398006689523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_385 : rowCell 3 385 ≤ (10420113461811147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75560722105463981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67335398006689523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_385_1
  · norm_num [gridPoint]

theorem exp_3_386_0 : expNegUpper (176860757164122281377207 / 1791639174180157696000 : ℝ) ≤ (134670789448990787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1081187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_386_1 : expNegUpper (2833079040531766346889 / 28666226786882523136 : ℝ) ≤ (119997817240809703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (541081 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_386 : rowCell 3 386 ≤ (742826544145863 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134670789448990787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119997817240809703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_386_1
  · norm_num [gridPoint]

theorem exp_3_387_0 : expNegUpper (2843203058020543577889 / 28768665630720987136 : ℝ) ≤ (14999726429157327 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (541081 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_387_1 : expNegUpper (88953903868481519432959 / 899020800960030848000 : ℝ) ≤ (2138238391249691 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_387 : rowCell 3 387 ≤ (8273230724210517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14999726429157327 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2138238391249691 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_387_1
  · norm_num [gridPoint]

theorem exp_3_388_0 : expNegUpper (9919023776585182785959 / 100247524934046848000 : ℝ) ≤ (53455957212501913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_388_1 : expNegUpper (39722439999148462176547 / 400990099736187392000 : ℝ) ≤ (9524277075342971 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1084117 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_388 : rowCell 3 388 ≤ (14741301266561339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53455957212501913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9524277075342971 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_388_1
  · norm_num [gridPoint]

theorem exp_3_389_0 : expNegUpper (14350997817363164346347 / 144870457188680192000 : ℝ) ≤ (95242766209140201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1084117 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_389_1 : expNegUpper (7183878472280793713229 / 72435228594340096000 : ℝ) ≤ (16967633444541161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_389 : rowCell 3 389 ≤ (13131663457313841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (95242766209140201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16967633444541161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_389_1
  · norm_num [gridPoint]

theorem exp_3_390_0 : expNegUpper (180235330337972089528821 / 1817317400057039104000 : ℝ) ≤ (84838163203496459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_390_1 : expNegUpper (360891516331375302678481 / 3634634800114078208000 : ℝ) ≤ (75562121849524341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2172159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_390 : rowCell 3 390 ≤ (584826644784869 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (84838163203496459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (75562121849524341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_390_1
  · norm_num [gridPoint]

theorem exp_3_391_0 : expNegUpper (1298107568727600136991 / 13073587845221888000 : ℝ) ≤ (75562118295058529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2172159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_391_1 : expNegUpper (32490568829451761413 / 326839696130547200 : ℝ) ≤ (67293151556548333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087063 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_391 : rowCell 3 391 ≤ (260428365602767 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75562118295058529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67293151556548333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_391_1
  · norm_num [gridPoint]

theorem exp_3_392_0 : expNegUpper (9096975210589663321907 / 91511251395637260800 : ℝ) ≤ (67293148413382031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087063 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_392_1 : expNegUpper (364303629022297396462311 / 3660450055825490432000 : ℝ) ≤ (7490342997006583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_392 : rowCell 3 392 ≤ (9276697168565897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (67293148413382031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7490342997006583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_392_1
  · norm_num [gridPoint]

theorem exp_3_393_0 : expNegUpper (365591660914041109754079 / 3673391941139829248000 : ℝ) ≤ (29961370598425991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_393_1 : expNegUpper (183009084490280583343619 / 1836695970569914624000 : ℝ) ≤ (416828005264501 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (272259 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_393 : rowCell 3 393 ≤ (1652048124510087 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29961370598425991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (416828005264501 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_393_1
  · norm_num [gridPoint]

theorem exp_3_394_0 : expNegUpper (816244398086006256851 / 8191903699466496000 : ℝ) ≤ (13338495554175769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (272259 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_394_1 : expNegUpper (1634392791128051621213 / 16383807398932992000 : ℝ) ≤ (11875082073098143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2180051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_394 : rowCell 3 394 ≤ (7354386933617853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13338495554175769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11875082073098143 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_394_1
  · norm_num [gridPoint]

theorem exp_3_395_0 : expNegUpper (369033973089910297091957 / 3699344226685772288000 : ℝ) ≤ (11875081530042297 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2180051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_395_1 : expNegUpper (92366066521096846862109 / 924836056671443072000 : ℝ) ≤ (8456899735825659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2182033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_395 : rowCell 3 395 ≤ (51149922581393 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11875081530042297 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8456899735825659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_395_1
  · norm_num [gridPoint]

theorem exp_3_396_0 : expNegUpper (92690913190000550252541 / 928088656729344128000 : ℝ) ≤ (21142248379485171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2182033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_396_1 : expNegUpper (74239168642925426288567 / 742470925383475302400 : ℝ) ≤ (1881875229942503 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1092009 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_396 : rowCell 3 396 ≤ (5827984143935359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21142248379485171 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1881875229942503 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_396_1
  · norm_num [gridPoint]

theorem exp_3_397_0 : expNegUpper (8277756180918159423703 / 82786397010105241600 : ℝ) ≤ (37637502901662499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1092009 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_397_1 : expNegUpper (20718506632603860749177 / 206965992525263104000 : ℝ) ≤ (4187219875670329 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_397 : rowCell 3 397 ≤ (5187247208847143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37637502901662499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4187219875670329 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_397_1
  · norm_num [gridPoint]

theorem exp_3_398_0 : expNegUpper (187120054613096931495217 / 1869221971148925184000 : ℝ) ≤ (3349775750538993 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186007 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_398_1 : expNegUpper (374676104593453120304553 / 3738443942297850368000 : ℝ) ≤ (1863143192835871 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547 / 250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_398 : rowCell 3 398 ≤ (4616479781563407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3349775750538993 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1863143192835871 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_398_1
  · norm_num [gridPoint]

theorem exp_3_399_0 : expNegUpper (601579049611153463217 / 6002436571914752000 : ℝ) ≤ (14905144879909521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547 / 250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_399_1 : expNegUpper (37642480882671665863 / 375152285744672000 : ℝ) ≤ (13263020699404033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_399 : rowCell 3 399 ≤ (821619176551923 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14905144879909521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13263020699404033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_399_1
  · norm_num [gridPoint]

theorem exp_3_400_0 : expNegUpper (2623190475527687328863 / 26143226464592672000 : ℝ) ≤ (26526040227494591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_400_1 : expNegUpper (42019915786555417243399 / 418291623433482752000 : ℝ) ≤ (2360123143808873 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547999 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_400 : rowCell 3 400 ≤ (3655325686074973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26526040227494591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2360123143808873 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_400_1
  · norm_num [gridPoint]

theorem exp_3_401_0 : expNegUpper (379497686625580692256439 / 3777749202661724672000 : ℝ) ≤ (5900307600790363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (547999 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_401_1 : expNegUpper (37993941434263805671539 / 377774920266172467200 : ℝ) ≤ (20996799825448377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_401 : rowCell 3 401 ≤ (3252128432813013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5900307600790363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20996799825448377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_401_1
  · norm_num [gridPoint]

theorem exp_3_402_0 : expNegUpper (38126169044809071194019 / 379089663272785971200 : ℝ) ≤ (10498399455553879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2193999 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_402_1 : expNegUpper (381705335609973209933461 / 3790896632727859712000 : ℝ) ≤ (4669474543071421 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_402 : rowCell 3 402 ≤ (2893114556556711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10498399455553879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4669474543071421 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_402_1
  · norm_num [gridPoint]

theorem exp_3_403_0 : expNegUpper (42559049992872853459621 / 422674100122194432000 : ℝ) ≤ (747115894582103 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1098003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_403_1 : expNegUpper (10652139329815079488163 / 105668525030548608000 : ℝ) ≤ (16613440347244313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_403 : rowCell 3 403 ≤ (514695210601091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (747115894582103 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16613440347244313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_403_1
  · norm_num [gridPoint]

theorem exp_3_404_0 : expNegUpper (3848069750812142465747 / 38172600077773952000 : ℝ) ≤ (16613439633751409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_404_1 : expNegUpper (15410178605003426334627 / 152690400311095808000 : ℝ) ≤ (2955139909666019 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220003 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_404 : rowCell 3 404 ≤ (1144462115168559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16613439633751409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2955139909666019 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_404_1
  · norm_num [gridPoint]

theorem exp_3_405_0 : expNegUpper (386588275876505054983587 / 3830475952760795648000 : ℝ) ≤ (2955139783627429 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220003 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_405_1 : expNegUpper (193518846678770123518973 / 1915237976380397824000 : ℝ) ≤ (13139948156505807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34407 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_405 : rowCell 3 405 ≤ (2035634065147133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2955139783627429 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13139948156505807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_405_1
  · norm_num [gridPoint]

theorem exp_3_406_0 : expNegUpper (21576409017448152949573 / 213539707558330624000 : ℝ) ≤ (3284986899983971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34407 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_406_1 : expNegUpper (8640593568067672762661 / 85415883023332249600 : ℝ) ≤ (11684135870540089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2204069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_406 : rowCell 3 406 ≤ (1810194469554601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3284986899983971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11684135870540089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_406_1
  · norm_num [gridPoint]

theorem exp_3_407_0 : expNegUpper (78033648877247597525989 / 771395271528972390400 : ℝ) ≤ (11684135379034519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2204069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_407_1 : expNegUpper (48827690841742423367517 / 482122044705607744000 : ℝ) ≤ (10388602091504169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1103047 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_407 : rowCell 3 407 ≤ (1609563847326753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11684135379034519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10388602091504169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_407_1
  · norm_num [gridPoint]

theorem exp_3_408_0 : expNegUpper (48995866510669675665693 / 483782602193190976000 : ℝ) ≤ (649287603593377 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1103047 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_408_1 : expNegUpper (392422151862561231628183 / 3870260817545527808000 : ℝ) ≤ (2308954736416207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1104061 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_408 : rowCell 3 408 ≤ (143103038169773 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (649287603593377 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2308954736416207 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_408_1
  · norm_num [gridPoint]

theorem exp_3_409_0 : expNegUpper (1750095268461171790703 / 17260302736675328000 : ℝ) ≤ (9235818562457133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1104061 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_409_1 : expNegUpper (876063546536109900251 / 8630151368337664000 : ℝ) ≤ (2052540427881221 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2210153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_409 : rowCell 3 409 ≤ (159022069462709 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9235818562457133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2052540427881221 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_409_1
  · norm_num [gridPoint]

theorem exp_3_410_0 : expNegUpper (197790882166897688553451 / 1948449126132062464000 : ℝ) ≤ (4105080686600877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2210153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_410_1 : expNegUpper (396040868962342704123501 / 3896898252264124928000 : ℝ) ≤ (7297703754831287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212189 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_410 : rowCell 3 410 ≤ (565423728991873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4105080686600877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7297703754831287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_410_1
  · norm_num [gridPoint]

theorem exp_3_411_0 : expNegUpper (397397928867791224650789 / 3910251227082056192000 : ℝ) ≤ (7297703456160689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212189 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_411_1 : expNegUpper (3978589809181796253889 / 39102512270820561920 : ℝ) ≤ (1621508344619741 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_411 : rowCell 3 411 ≤ (502561236903993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7297703456160689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1621508344619741 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_411_1
  · norm_num [gridPoint]

theorem exp_3_412_0 : expNegUpper (443577709997877602521 / 4359585600228602880 : ℝ) ≤ (1297206622967129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2214227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_412_1 : expNegUpper (44409215755677651737579 / 435958560022860288000 : ℝ) ≤ (180127820811219 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_412 : rowCell 3 412 ≤ (223322500724443 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1297206622967129 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (180127820811219 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_412_1
  · norm_num [gridPoint]

theorem exp_3_413_0 : expNegUpper (401047804717029876690299 / 3937025691635184128000 : ℝ) ≤ (5764090033254511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_413_1 : expNegUpper (200756380801719535800249 / 1968512845817592064000 : ℝ) ≤ (2561009720272777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_413 : rowCell 3 413 ≤ (396912441659241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5764090033254511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2561009720272777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_413_1
  · norm_num [gridPoint]

theorem exp_3_414_0 : expNegUpper (8057630720338999492881 / 79008943627407616000 : ℝ) ≤ (2561009617583123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443663 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_414_1 : expNegUpper (16133938012701555600193 / 158017887254815232000 : ℝ) ≤ (1137760220168599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444073 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_414 : rowCell 3 414 ≤ (88171029285881 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2561009617583123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1137760220168599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_414_1
  · norm_num [gridPoint]

theorem exp_3_415_0 : expNegUpper (44969015876687642539913 / 440432389934592512000 : ℝ) ≤ (4551040699426619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444073 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_415_1 : expNegUpper (1406909784499086692987 / 13763512185456016000 : ℝ) ≤ (25270832047089 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2222417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_415 : rowCell 3 415 ≤ (626709460969721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4551040699426619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25270832047089 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_415_1
  · norm_num [gridPoint]

theorem sum_3_384_2 : blockSum (rowCell 3) 384 2 ≤ (22112413289169687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_384) (by simpa only [blockSum_one] using cell_3_385) (by norm_num)

theorem sum_3_386_2 : blockSum (rowCell 3) 386 2 ≤ (35117125052067609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_386) (by simpa only [blockSum_one] using cell_3_387) (by norm_num)

theorem sum_3_384_4 : blockSum (rowCell 3) 384 4 ≤ (79341951630406983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_384_2 sum_3_386_2 (by norm_num)

theorem sum_3_388_2 : blockSum (rowCell 3) 388 2 ≤ (1393648236193759 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_388) (by simpa only [blockSum_one] using cell_3_389) (by norm_num)

theorem sum_3_390_2 : blockSum (rowCell 3) 390 2 ≤ (1105683375990403 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_390) (by simpa only [blockSum_one] using cell_3_391) (by norm_num)

theorem sum_3_388_4 : blockSum (rowCell 3) 388 4 ≤ (1249665806092081 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_388_2 sum_3_390_2 (by norm_num)

theorem sum_3_384_8 : blockSum (rowCell 3) 384 8 ≤ (129328583874090223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_384_4 sum_3_388_4 (by norm_num)

theorem sum_3_392_2 : blockSum (rowCell 3) 392 2 ≤ (4384234447779083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_392) (by simpa only [blockSum_one] using cell_3_393) (by norm_num)

theorem sum_3_394_2 : blockSum (rowCell 3) 394 2 ≤ (13901577024036157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_394) (by simpa only [blockSum_one] using cell_3_395) (by norm_num)

theorem sum_3_392_4 : blockSum (rowCell 3) 392 4 ≤ (31438514815152489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_392_2 sum_3_394_2 (by norm_num)

theorem sum_3_396_2 : blockSum (rowCell 3) 396 2 ≤ (5507615676391251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_396) (by simpa only [blockSum_one] using cell_3_397) (by norm_num)

theorem sum_3_398_2 : blockSum (rowCell 3) 398 2 ≤ (4362287832161511 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_398) (by simpa only [blockSum_one] using cell_3_399) (by norm_num)

theorem sum_3_396_4 : blockSum (rowCell 3) 396 4 ≤ (4934951754276381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_396_2 sum_3_398_2 (by norm_num)

theorem sum_3_392_8 : blockSum (rowCell 3) 392 8 ≤ (51178321832258013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_392_4 sum_3_396_4 (by norm_num)

theorem sum_3_384_16 : blockSum (rowCell 3) 384 16 ≤ (45126726426587059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_384_8 sum_3_392_8 (by norm_num)

theorem sum_3_400_2 : blockSum (rowCell 3) 400 2 ≤ (3453727059443993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_400) (by simpa only [blockSum_one] using cell_3_401) (by norm_num)

theorem sum_3_402_2 : blockSum (rowCell 3) 402 2 ≤ (2733295304781083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_402) (by simpa only [blockSum_one] using cell_3_403) (by norm_num)

theorem sum_3_400_4 : blockSum (rowCell 3) 400 4 ≤ (1546755591056269 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_400_2 sum_3_402_2 (by norm_num)

theorem sum_3_404_2 : blockSum (rowCell 3) 404 2 ≤ (4324558295484251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_404) (by simpa only [blockSum_one] using cell_3_405) (by norm_num)

theorem sum_3_406_2 : blockSum (rowCell 3) 406 2 ≤ (1709879158440677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_406) (by simpa only [blockSum_one] using cell_3_407) (by norm_num)

theorem sum_3_404_4 : blockSum (rowCell 3) 404 4 ≤ (1548863322473121 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_404_2 sum_3_406_2 (by norm_num)

theorem sum_3_400_8 : blockSum (rowCell 3) 400 8 ≤ (20118361340815757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_400_4 sum_3_404_4 (by norm_num)

theorem sum_3_408_2 : blockSum (rowCell 3) 408 2 ≤ (1351603468699701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_408) (by simpa only [blockSum_one] using cell_3_409) (by norm_num)

theorem sum_3_410_2 : blockSum (rowCell 3) 410 2 ≤ (533992482947933 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_410) (by simpa only [blockSum_one] using cell_3_411) (by norm_num)

theorem sum_3_408_4 : blockSum (rowCell 3) 408 4 ≤ (2419588434595567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_408_2 sum_3_410_2 (by norm_num)

theorem sum_3_412_2 : blockSum (rowCell 3) 412 2 ≤ (843557443108127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_412) (by simpa only [blockSum_one] using cell_3_413) (by norm_num)

theorem sum_3_414_2 : blockSum (rowCell 3) 414 2 ≤ (1332077695256769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_414) (by simpa only [blockSum_one] using cell_3_415) (by norm_num)

theorem sum_3_412_4 : blockSum (rowCell 3) 412 4 ≤ (3019192581473023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_412_2 sum_3_414_2 (by norm_num)

theorem sum_3_408_8 : blockSum (rowCell 3) 408 8 ≤ (7858369450664157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_408_4 sum_3_412_4 (by norm_num)

theorem sum_3_400_16 : blockSum (rowCell 3) 400 16 ≤ (13988365395739957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_400_8 sum_3_408_8 (by norm_num)

theorem sum_3_384_32 : blockSum (rowCell 3) 384 32 ≤ (4169672729956563 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_384_16 sum_3_400_16 (by norm_num)

#print axioms sum_3_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
