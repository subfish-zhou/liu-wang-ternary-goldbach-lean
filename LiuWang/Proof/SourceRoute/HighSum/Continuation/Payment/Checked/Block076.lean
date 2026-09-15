import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_384_0 : expNegUpper (109917686122421937689 / 1111792860099364000 : ℝ) ≤ (57912031097357693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2164923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_384_1 : expNegUpper (14085752364451116086503 / 142309486092718592000 : ℝ) ≤ (20659512116740849 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_384 : rowCell 4 384 ≤ (639141824003413 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57912031097357693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20659512116740849 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_384_1
  · norm_num [gridPoint]

theorem exp_4_385_0 : expNegUpper (353406709177512404120327 / 3570496331186262528000 : ℝ) ≤ (103297555399729199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2166859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_385_1 : expNegUpper (176907891759306453873863 / 1785248165593131264000 : ℝ) ≤ (5757217395711061 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2711 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_385 : rowCell 4 385 ≤ (3562423496517439 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (103297555399729199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5757217395711061 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_385_1
  · norm_num [gridPoint]

theorem exp_4_386_0 : expNegUpper (177541204279386281377207 / 1791639174180157696000 : ℝ) ≤ (2878608554422629 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2711 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_386_1 : expNegUpper (2843946776417803338889 / 28666226786882523136 : ℝ) ≤ (82134707174417779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (271343 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_386 : rowCell 4 386 ≤ (12706479745287401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2878608554422629 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (82134707174417779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_386_1
  · norm_num [gridPoint]

theorem exp_4_387_0 : expNegUpper (2854109629822954585889 / 28768665630720987136 : ℝ) ≤ (20533675777749423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (271343 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_387_1 : expNegUpper (89294127426113519432959 / 899020800960030848000 : ℝ) ≤ (73227233828181963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2172691 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_387 : rowCell 4 387 ≤ (1770176878843 / 156250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20533675777749423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73227233828181963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_387_1
  · norm_num [gridPoint]

theorem exp_4_388_0 : expNegUpper (89612651169285333073631 / 902227724406421632000 : ℝ) ≤ (36613615115584409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2172691 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_388_1 : expNegUpper (358865281467637535588923 / 3608910897625686528000 : ℝ) ≤ (65278567543210637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2174643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_388 : rowCell 4 388 ≤ (5049983606255219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36613615115584409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65278567543210637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_388_1
  · norm_num [gridPoint]

theorem exp_4_389_0 : expNegUpper (14405724855957089466347 / 144870457188680192000 : ℝ) ≤ (8159820544922549 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2174643 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_389_1 : expNegUpper (7211193446682288753229 / 72435228594340096000 : ℝ) ≤ (454580664646557 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_389 : rowCell 4 389 ≤ (2250792665756017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8159820544922549 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (454580664646557 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_389_1
  · norm_num [gridPoint]

theorem exp_4_390_0 : expNegUpper (180920631942782841528821 / 1817317400057039104000 : ℝ) ≤ (29093161128462027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088299 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_390_1 : expNegUpper (362259692296223430678481 / 3634634800114078208000 : ℝ) ≤ (51858962219194057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (544639 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_390 : rowCell 4 390 ≤ (1604920202561761 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29093161128462027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51858962219194057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_390_1
  · norm_num [gridPoint]

theorem exp_4_391_0 : expNegUpper (11727259423528881232919 / 117662290606996992000 : ℝ) ≤ (51858959725522017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (544639 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_391_1 : expNegUpper (293520444634115452717 / 2941557265174924800 : ℝ) ≤ (23107318452037769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1090259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_391 : rowCell 4 391 ≤ (3575807389613613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51858959725522017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23107318452037769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_391_1
  · norm_num [gridPoint]

theorem exp_4_392_0 : expNegUpper (9131361653068869721907 / 91511251395637260800 : ℝ) ≤ (46214634697487017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1090259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_392_1 : expNegUpper (365676659476692276462311 / 3660450055825490432000 : ℝ) ≤ (41180190337949229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545621 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_392 : rowCell 4 392 ≤ (6372909160372129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46214634697487017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41180190337949229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_392_1
  · norm_num [gridPoint]

theorem exp_4_393_0 : expNegUpper (366969545857982741754079 / 3673391941139829248000 : ℝ) ≤ (20590094192790161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545621 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_393_1 : expNegUpper (183696813339864711343619 / 1836695970569914624000 : ℝ) ≤ (4586279261673061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2184453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_393 : rowCell 4 393 ≤ (567838116887381 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20590094192790161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4586279261673061 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_393_1
  · norm_num [gridPoint]

theorem exp_4_394_0 : expNegUpper (7373805826548356471659 / 73727133295198464000 : ℝ) ≤ (2293139522881927 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2184453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_394_1 : expNegUpper (14764650517910129870917 / 147454266590396928000 : ℝ) ≤ (8171583056892587 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1093213 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_394 : rowCell 4 394 ≤ (1264750355169621 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2293139522881927 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8171583056892587 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_394_1
  · norm_num [gridPoint]

theorem exp_4_395_0 : expNegUpper (370416712523398681091957 / 3699344226685772288000 : ℝ) ≤ (1307453227983373 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1093213 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_395_1 : expNegUpper (92711144568275598862109 / 924836056671443072000 : ℝ) ≤ (14558134326130323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_395 : rowCell 4 395 ≤ (4506701070509391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1307453227983373 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14558134326130323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_395_1
  · norm_num [gridPoint]

theorem exp_4_396_0 : expNegUpper (93037204859565990252541 / 928088656729344128000 : ℝ) ≤ (3639533412587007 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_396_1 : expNegUpper (74515716529623103088567 / 742470925383475302400 : ℝ) ≤ (25933390961233053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_396 : rowCell 4 396 ≤ (62722977174019 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3639533412587007 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25933390961233053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_396_1
  · norm_num [gridPoint]

theorem exp_4_397_0 : expNegUpper (74777324412870462013327 / 745077573090947174400 : ℝ) ≤ (12966694882915987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_397_1 : expNegUpper (187159143032565626742593 / 1862693932727367936000 : ℝ) ≤ (23096022819674153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2192367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_397 : rowCell 4 397 ≤ (3575268815597977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12966694882915987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23096022819674153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_397_1
  · norm_num [gridPoint]

theorem exp_4_398_0 : expNegUpper (187815065197001187495217 / 1869221971148925184000 : ℝ) ≤ (11548010881245639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2192367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_398_1 : expNegUpper (376063698516488256304553 / 3738443942297850368000 : ℝ) ≤ (2056693782594441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1097177 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_398 : rowCell 4 398 ≤ (1591971120814493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11548010881245639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2056693782594441 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_398_1
  · norm_num [gridPoint]

theorem exp_4_399_0 : expNegUpper (603806967071284484017 / 6002436571914752000 : ℝ) ≤ (10283468445542339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1097177 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_399_1 : expNegUpper (37781482999452517063 / 375152285744672000 : ℝ) ≤ (9156444240482159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439269 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_399 : rowCell 4 399 ≤ (2835151797222921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10283468445542339 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9156444240482159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_399_1
  · norm_num [gridPoint]

theorem exp_4_400_0 : expNegUpper (23695894008333889959767 / 235289038181334048000 : ℝ) ≤ (18312887654350111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439269 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_400_1 : expNegUpper (379571690491580643190591 / 3764624610901344768000 : ℝ) ≤ (2038023069009183 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_400 : rowCell 4 400 ≤ (1262154003284109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18312887654350111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2038023069009183 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_400_1
  · norm_num [gridPoint]

theorem exp_4_401_0 : expNegUpper (16560651718596057924193 / 164249965333118464000 : ℝ) ≤ (16304183821238071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2198339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_401_1 : expNegUpper (1657975173913014437893 / 16424996533311846400 : ℝ) ≤ (14514315703934479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2200337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_401 : rowCell 4 401 ≤ (1797850139097 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16304183821238071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14514315703934479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_401_1
  · norm_num [gridPoint]

theorem exp_4_402_0 : expNegUpper (38266142059499272794019 / 379089663272785971200 : ℝ) ≤ (1814289382229859 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2200337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_402_1 : expNegUpper (383102638512101849933461 / 3790896632727859712000 : ℝ) ≤ (6459806897728031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2202339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_402 : rowCell 4 402 ≤ (2000506739652721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1814289382229859 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6459806897728031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_402_1
  · norm_num [gridPoint]

theorem exp_4_403_0 : expNegUpper (384433607327531073136589 / 3804066901099749888000 : ℝ) ≤ (645980661216319 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2202339 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_403_1 : expNegUpper (96219186505061219393467 / 951016725274937472000 : ℝ) ≤ (11498950714720127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (275543 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_403 : rowCell 4 403 ≤ (1780623620988811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (645980661216319 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11498950714720127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_403_1
  · norm_num [gridPoint]

theorem exp_4_404_0 : expNegUpper (3862115597176630145747 / 38172600077773952000 : ℝ) ≤ (2299790041980709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (275543 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_404_1 : expNegUpper (15466264900670442014627 / 152690400311095808000 : ℝ) ≤ (5116734024430509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2206353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_404 : rowCell 4 404 ≤ (792373732324321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2299790041980709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5116734024430509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_404_1
  · norm_num [gridPoint]

theorem exp_4_405_0 : expNegUpper (387995287757727198983587 / 3830475952760795648000 : ℝ) ≤ (2558366900674481 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2206353 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_405_1 : expNegUpper (194221138996994507518973 / 1915237976380397824000 : ℝ) ≤ (9106335267576031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_405 : rowCell 4 405 ≤ (1410275800904519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2558366900674481 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9106335267576031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_405_1
  · norm_num [gridPoint]

theorem exp_4_406_0 : expNegUpper (194892400720031136546157 / 1921857368024975616000 : ℝ) ≤ (2276583718321673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441673 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_406_1 : expNegUpper (78046744488853483663949 / 768742947209990246400 : ℝ) ≤ (63301042513961 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2210381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_406 : rowCell 4 406 ≤ (627443069313901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2276583718321673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (63301042513961 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_406_1
  · norm_num [gridPoint]

theorem exp_4_407_0 : expNegUpper (78316022151401376725989 / 771395271528972390400 : ℝ) ≤ (2025633273342771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2210381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_407_1 : expNegUpper (49003870732491863367517 / 482122044705607744000 : ℝ) ≤ (7208661826833701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_407 : rowCell 4 407 ≤ (55825304486651 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2025633273342771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7208661826833701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_407_1
  · norm_num [gridPoint]

theorem exp_4_408_0 : expNegUpper (49172653212612459665693 / 483782602193190976000 : ℝ) ≤ (7208661518981169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2212401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_408_1 : expNegUpper (393834018233330127628183 / 3870260817545527808000 : ℝ) ≤ (6412764915984307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (276803 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_408 : rowCell 4 408 ≤ (248321663409499 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7208661518981169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6412764915984307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_408_1
  · norm_num [gridPoint]

theorem exp_4_409_0 : expNegUpper (15807526250563172036327 / 155342724630077952000 : ℝ) ≤ (1603191160999123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (276803 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_409_1 : expNegUpper (7912857791135834542259 / 77671362315038976000 : ℝ) ≤ (5704177818170719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44329 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_409 : rowCell 4 409 ≤ (883578330656727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1603191160999123 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5704177818170719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_409_1
  · norm_num [gridPoint]

theorem exp_4_410_0 : expNegUpper (198500456219442200553451 / 1948449126132062464000 : ℝ) ≤ (5704177577890317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (44329 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_410_1 : expNegUpper (397457589822658352123501 / 3896898252264124928000 : ℝ) ≤ (507338803655347 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2218481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_410 : rowCell 4 410 ≤ (196477441893587 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5704177577890317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (507338803655347 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_410_1
  · norm_num [gridPoint]

theorem exp_4_411_0 : expNegUpper (398819504217653624650789 / 3910251227082056192000 : ℝ) ≤ (126834695607563 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2218481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_411_1 : expNegUpper (3992781290232686493889 / 39102512270820561920 : ℝ) ≤ (4511911924367013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1110257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_411 : rowCell 4 411 ≤ (349484334732863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (126834695607563 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4511911924367013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_411_1
  · norm_num [gridPoint]

theorem exp_4_412_0 : expNegUpper (4006439415927256182689 / 39236270402057425920 : ℝ) ≤ (563988967111493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1110257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_412_1 : expNegUpper (401104517150961265638211 / 3923627040205742592000 : ℝ) ≤ (4012184273806293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277819 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_412 : rowCell 4 412 ≤ (310792369733813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (563988967111493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4012184273806293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_412_1
  · norm_num [gridPoint]

theorem exp_4_413_0 : expNegUpper (402474234556439028690299 / 3937025691635184128000 : ℝ) ≤ (4012184108229223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (277819 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_413_1 : expNegUpper (201468382099037423800249 / 1968512845817592064000 : ℝ) ≤ (445932456821871 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224593 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_413 : rowCell 4 413 ≤ (4421715464159 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4012184108229223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (445932456821871 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_413_1
  · norm_num [gridPoint]

theorem exp_4_414_0 : expNegUpper (8086207862022650052881 / 79008943627407616000 : ℝ) ≤ (1783729754175283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2224593 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_414_1 : expNegUpper (16190995206277921680193 / 158017887254815232000 : ℝ) ≤ (634344852600021 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_414 : rowCell 4 414 ≤ (491427335342311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1783729754175283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (634344852600021 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_414_1
  · norm_num [gridPoint]

theorem exp_4_415_0 : expNegUpper (406152427219144686859217 / 3963891509411332608000 : ℝ) ≤ (3171724133877377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2226637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_415_1 : expNegUpper (12706839844372484236883 / 123871609669104144000 : ℝ) ≤ (2819617172015261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (445737 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_415 : rowCell 4 415 ≤ (109223497717849 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3171724133877377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2819617172015261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_415_1
  · norm_num [gridPoint]

theorem sum_4_384_2 : blockSum (rowCell 4) 384 2 ≤ (30228239586155081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_384) (by simpa only [blockSum_one] using cell_4_385) (by norm_num)

theorem sum_4_386_2 : blockSum (rowCell 4) 386 2 ≤ (24035611769882601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_386) (by simpa only [blockSum_one] using cell_4_387) (by norm_num)

theorem sum_4_384_4 : blockSum (rowCell 4) 384 4 ≤ (27131925678018841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_384_2 sum_4_386_2 (by norm_num)

theorem sum_4_388_2 : blockSum (rowCell 4) 388 2 ≤ (9551568937767253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_388) (by simpa only [blockSum_one] using cell_4_389) (by norm_num)

theorem sum_4_390_2 : blockSum (rowCell 4) 390 2 ≤ (15176215792036031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_390) (by simpa only [blockSum_one] using cell_4_391) (by norm_num)

theorem sum_4_388_4 : blockSum (rowCell 4) 388 4 ≤ (34279353667570537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_388_2 sum_4_390_2 (by norm_num)

theorem sum_4_384_8 : blockSum (rowCell 4) 384 8 ≤ (88543205023608219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_384_4 sum_4_388_4 (by norm_num)

theorem sum_4_392_2 : blockSum (rowCell 4) 392 2 ≤ (12051290329245939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_392) (by simpa only [blockSum_one] using cell_4_393) (by norm_num)

theorem sum_4_394_2 : blockSum (rowCell 4) 394 2 ≤ (76525619929503 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_394) (by simpa only [blockSum_one] using cell_4_395) (by norm_num)

theorem sum_4_392_4 : blockSum (rowCell 4) 392 4 ≤ (10808496410216907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_392_2 sum_4_394_2 (by norm_num)

theorem sum_4_396_2 : blockSum (rowCell 4) 396 2 ≤ (7589539354735193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_396) (by simpa only [blockSum_one] using cell_4_397) (by norm_num)

theorem sum_4_398_2 : blockSum (rowCell 4) 398 2 ≤ (6019094038851907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_398) (by simpa only [blockSum_one] using cell_4_399) (by norm_num)

theorem sum_4_396_4 : blockSum (rowCell 4) 396 4 ≤ (136086333935871 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_396_2 sum_4_398_2 (by norm_num)

theorem sum_4_392_8 : blockSum (rowCell 4) 392 8 ≤ (17612813107010457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_392_4 sum_4_396_4 (by norm_num)

theorem sum_4_384_16 : blockSum (rowCell 4) 384 16 ≤ (123768831237629133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_384_8 sum_4_392_8 (by norm_num)

theorem sum_4_400_2 : blockSum (rowCell 4) 400 2 ≤ (1192905170109867 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_400) (by simpa only [blockSum_one] using cell_4_401) (by norm_num)

theorem sum_4_402_2 : blockSum (rowCell 4) 402 2 ≤ (945282590160383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_402) (by simpa only [blockSum_one] using cell_4_403) (by norm_num)

theorem sum_4_400_4 : blockSum (rowCell 4) 400 4 ≤ (8552751041081 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_400_2 sum_4_402_2 (by norm_num)

theorem sum_4_404_2 : blockSum (rowCell 4) 404 2 ≤ (2995023265553161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_404) (by simpa only [blockSum_one] using cell_4_405) (by norm_num)

theorem sum_4_406_2 : blockSum (rowCell 4) 406 2 ≤ (1185696114180411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_406) (by simpa only [blockSum_one] using cell_4_407) (by norm_num)

theorem sum_4_404_4 : blockSum (rowCell 4) 404 4 ≤ (5366415493913983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_404_2 sum_4_406_2 (by norm_num)

theorem sum_4_400_8 : blockSum (rowCell 4) 400 8 ≤ (13919166534994983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_400_4 sum_4_404_4 (by norm_num)

theorem sum_4_408_2 : blockSum (rowCell 4) 408 2 ≤ (1876864984294723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_408) (by simpa only [blockSum_one] using cell_4_409) (by norm_num)

theorem sum_4_410_2 : blockSum (rowCell 4) 410 2 ≤ (742439218520037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_410) (by simpa only [blockSum_one] using cell_4_411) (by norm_num)

theorem sum_4_408_4 : blockSum (rowCell 4) 408 4 ≤ (3361743421334797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_408_2 sum_4_410_2 (by norm_num)

theorem sum_4_412_2 : blockSum (rowCell 4) 412 2 ≤ (1174299172487501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_412) (by simpa only [blockSum_one] using cell_4_413) (by norm_num)

theorem sum_4_414_2 : blockSum (rowCell 4) 414 2 ≤ (928321326213707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_414) (by simpa only [blockSum_one] using cell_4_415) (by norm_num)

theorem sum_4_412_4 : blockSum (rowCell 4) 412 4 ≤ (262827562337651 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_412_2 sum_4_414_2 (by norm_num)

theorem sum_4_408_8 : blockSum (rowCell 4) 408 8 ≤ (1092872784007201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_408_4 sum_4_412_4 (by norm_num)

theorem sum_4_400_16 : blockSum (rowCell 4) 400 16 ≤ (4845882613757747 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_400_8 sum_4_408_8 (by norm_num)

theorem sum_4_384_32 : blockSum (rowCell 4) 384 32 ≤ (143152361692660121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_384_16 sum_4_400_16 (by norm_num)

#print axioms sum_4_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
