import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_384_0 : expNegUpper (110553329751006897689 / 1111792860099364000 : ℝ) ≤ (16347083552761283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1087307 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_384_1 : expNegUpper (14166969114223588406503 / 142309486092718592000 : ℝ) ≤ (58376222561074967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_384 : rowCell 6 384 ≤ (9025022674541973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16347083552761283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58376222561074967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_384_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_384_1
  · norm_num [gridPoint]

theorem exp_6_385_0 : expNegUpper (355444409656144340120327 / 3570496331186262528000 : ℝ) ≤ (2918810976797053 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1088271 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_385_1 : expNegUpper (177924921565042389873863 / 1785248165593131264000 : ℝ) ≤ (52110037813311757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_385 : rowCell 6 385 ≤ (8056757150904353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2918810976797053 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52110037813311757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_385_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_385_1
  · norm_num [gridPoint]

theorem exp_6_386_0 : expNegUpper (178561874952282281377207 / 1791639174180157696000 : ℝ) ≤ (52110035132148147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1089237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_386_1 : expNegUpper (2860248380246858826889 / 28666226786882523136 : ℝ) ≤ (5813889542491091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2180409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_386 : rowCell 6 386 ≤ (3595771485142311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (52110035132148147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5813889542491091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_386_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_386_1
  · norm_num [gridPoint]

theorem exp_6_387_0 : expNegUpper (2870469487526571097889 / 28768665630720987136 : ℝ) ≤ (46511113963867919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2180409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_387_1 : expNegUpper (89804462762561519432959 / 899020800960030848000 : ℝ) ≤ (518862632113737 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545587 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_387 : rowCell 6 387 ≤ (320925328076229 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46511113963867919 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (518862632113737 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_387_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_387_1
  · norm_num [gridPoint]

theorem exp_6_388_0 : expNegUpper (90124806939313365073631 / 902227724406421632000 : ℝ) ≤ (8301801692727249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (545587 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_388_1 : expNegUpper (360910263680589599588923 / 3608910897625686528000 : ℝ) ≤ (37040642197421221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2184291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_388 : rowCell 6 388 ≤ (5727911098156077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8301801692727249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37040642197421221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_388_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_388_1
  · norm_num [gridPoint]

theorem exp_6_389_0 : expNegUpper (14487815413847977146347 / 144870457188680192000 : ℝ) ≤ (37040640331928437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2184291 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_389_1 : expNegUpper (7252165908284531313229 / 72435228594340096000 : ℝ) ≤ (33049538974773487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_389 : rowCell 6 389 ≤ (39929990989767 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37040640331928437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33049538974773487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_389_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_389_1
  · norm_num [gridPoint]

theorem exp_6_390_0 : expNegUpper (181948584349998969528821 / 1817317400057039104000 : ℝ) ≤ (33049537322066547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2186237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_390_1 : expNegUpper (364311956243495622678481 / 3634634800114078208000 : ℝ) ≤ (29485149680686939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_390 : rowCell 6 390 ≤ (4560085559748639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33049537322066547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29485149680686939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_390_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_390_1
  · norm_num [gridPoint]

theorem exp_6_391_0 : expNegUpper (620720862157873749101 / 6192752137210368000 : ℝ) ≤ (5897029643328251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2188187 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_391_1 : expNegUpper (15535706967773150143 / 154818803430259200 : ℝ) ≤ (13151114687920623 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_391 : rowCell 6 391 ≤ (101701642387897 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5897029643328251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13151114687920623 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_391_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_391_1
  · norm_num [gridPoint]

theorem exp_6_392_0 : expNegUpper (9182941316787679321907 / 91511251395637260800 : ℝ) ≤ (3287778509881221 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2190141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_392_1 : expNegUpper (367736205158284596462311 / 3660450055825490432000 : ℝ) ≤ (4692057560679601 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1096049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_392 : rowCell 6 392 ≤ (725745473331691 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3287778509881221 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4692057560679601 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_392_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_392_1
  · norm_num [gridPoint]

theorem exp_6_393_0 : expNegUpper (369036373273895189754079 / 3673391941139829248000 : ℝ) ≤ (4692057330973441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1096049 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_393_1 : expNegUpper (184728406614240903343619 / 1836695970569914624000 : ℝ) ≤ (20923094528078113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109703 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_393 : rowCell 6 393 ≤ (647295206310881 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4692057330973441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20923094528078113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_393_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_393_1
  · norm_num [gridPoint]

theorem exp_6_394_0 : expNegUpper (7415215192209806711659 / 73727133295198464000 : ℝ) ≤ (20923093510957721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (109703 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_394_1 : expNegUpper (14847323614546627790917 / 147454266590396928000 : ℝ) ≤ (9329117521851957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274503 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_394 : rowCell 6 394 ≤ (14431530197779 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20923093510957721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9329117521851957 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_394_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_394_1
  · norm_num [gridPoint]

theorem exp_6_395_0 : expNegUpper (372490821673631257091957 / 3699344226685772288000 : ℝ) ≤ (4664558535761677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274503 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_395_1 : expNegUpper (93228761639043726862109 / 924836056671443072000 : ℝ) ≤ (16636712659202571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274749 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_395 : rowCell 6 395 ≤ (1286869615561893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4664558535761677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16636712659202571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_395_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_395_1
  · norm_num [gridPoint]

theorem exp_6_396_0 : expNegUpper (93556642363914150252541 / 928088656729344128000 : ℝ) ≤ (3327342372350177 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (274749 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_396_1 : expNegUpper (74930538359669618288567 / 742470925383475302400 : ℝ) ≤ (7416295747492897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (549991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_396 : rowCell 6 396 ≤ (1147384936987737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3327342372350177 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7416295747492897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_396_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_396_1
  · norm_num [gridPoint]

theorem exp_6_397_0 : expNegUpper (75193602589781002813327 / 745077573090947174400 : ℝ) ≤ (14832590788981813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (549991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_397_1 : expNegUpper (188198018041261946742593 / 1862693932727367936000 : ℝ) ≤ (1652834548971783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110097 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_397 : rowCell 6 397 ≤ (2045815288724841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14832590788981813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1652834548971783 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_397_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_397_1
  · norm_num [gridPoint]

theorem exp_6_398_0 : expNegUpper (188857581072857571495217 / 1869221971148925184000 : ℝ) ≤ (6611337883395731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110097 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_398_1 : expNegUpper (378145089401040960304553 / 3738443942297850368000 : ℝ) ≤ (11786225957378793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2203919 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_398 : rowCell 6 398 ≤ (911835791330819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6611337883395731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11786225957378793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_398_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_398_1
  · norm_num [gridPoint]

theorem exp_6_399_0 : expNegUpper (607148843261481015217 / 6002436571914752000 : ℝ) ≤ (2357245080834437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2203919 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_399_1 : expNegUpper (37989986174623793863 / 375152285744672000 : ℝ) ≤ (10504695358254867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1102951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_399 : rowCell 6 399 ≤ (203184246124413 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2357245080834437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10504695358254867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_399_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_399_1
  · norm_num [gridPoint]

theorem exp_6_400_0 : expNegUpper (23826663601210945959767 / 235289038181334048000 : ℝ) ≤ (2100938973725597 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1102951 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_400_1 : expNegUpper (381660363110453475190591 / 3764624610901344768000 : ℝ) ≤ (936150580594381 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2207889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_400 : rowCell 6 400 ≤ (362165300432361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2100938973725597 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (936150580594381 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_400_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_400_1
  · norm_num [gridPoint]

theorem exp_6_401_0 : expNegUpper (382990943880902292256439 / 3777749202661724672000 : ℝ) ≤ (9361505372630553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2207889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_401_1 : expNegUpper (38342660348602621671539 / 377774920266172467200 : ℝ) ≤ (8341837997534927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2209879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_401 : rowCell 6 401 ≤ (645471851950013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9361505372630553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8341837997534927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_401_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_401_1
  · norm_num [gridPoint]

theorem exp_6_402_0 : expNegUpper (38476101581534575194019 / 379089663272785971200 : ℝ) ≤ (8341837614094631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2209879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_402_1 : expNegUpper (385198592865294809933461 / 3790896632727859712000 : ℝ) ≤ (929055880925119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69121 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_402 : rowCell 6 402 ≤ (575137504862567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8341837614094631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (929055880925119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_402_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_402_1
  · norm_num [gridPoint]

theorem exp_6_403_0 : expNegUpper (386536843415044161136589 / 3804066901099749888000 : ℝ) ≤ (232263959628913 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69121 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_403_1 : expNegUpper (96744085310149475393467 / 951016725274937472000 : ℝ) ≤ (165537417442993 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221387 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_403 : rowCell 6 403 ≤ (128103272467999 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (232263959628913 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (165537417442993 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_403_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_403_1
  · norm_num [gridPoint]

theorem exp_6_404_0 : expNegUpper (3883184366723361665747 / 38172600077773952000 : ℝ) ≤ (82768704969371 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221387 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_404_1 : expNegUpper (15550394344170965534627 / 152690400311095808000 : ℝ) ≤ (2949205410224371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2215871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_404 : rowCell 6 404 ≤ (912962882690587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82768704969371 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2949205410224371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_404_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_404_1
  · norm_num [gridPoint]

theorem exp_6_405_0 : expNegUpper (390105805579560414983587 / 3830475952760795648000 : ℝ) ≤ (2949205277450809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2215871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_405_1 : expNegUpper (195274577474331083518973 / 1915237976380397824000 : ℝ) ≤ (656717553243679 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17743 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_405 : rowCell 6 405 ≤ (406612434517153 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2949205277450809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (656717553243679 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_405_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_405_1
  · norm_num [gridPoint]

theorem exp_6_406_0 : expNegUpper (195949480064527776546157 / 1921857368024975616000 : ℝ) ≤ (5253740191053341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (17743 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_406_1 : expNegUpper (78468848053220126863949 / 768742947209990246400 : ℝ) ≤ (4679044575605809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (554971 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_406 : rowCell 6 406 ≤ (7243075891711 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5253740191053341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4679044575605809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_406_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_406_1
  · norm_num [gridPoint]

theorem exp_6_407_0 : expNegUpper (78739582062632045525989 / 771395271528972390400 : ℝ) ≤ (4679044367841893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (554971 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_407_1 : expNegUpper (49268140568616023367517 / 482122044705607744000 : ℝ) ≤ (4166783759571199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444379 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_407 : rowCell 6 407 ≤ (645045734474671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4679044367841893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4166783759571199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_407_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_407_1
  · norm_num [gridPoint]

theorem exp_6_408_0 : expNegUpper (49437833265526635665693 / 483782602193190976000 : ℝ) ≤ (4166783575822269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444379 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_408_1 : expNegUpper (395951817789483471628183 / 3870260817545527808000 : ℝ) ≤ (3710224448031279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2223911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_408 : rowCell 6 408 ≤ (287199251049399 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4166783575822269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3710224448031279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_408_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_408_1
  · norm_num [gridPoint]

theorem exp_6_409_0 : expNegUpper (15892529502182110916327 / 155342724630077952000 : ℝ) ≤ (1855112142768123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2223911 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_409_1 : expNegUpper (7955286599602102702259 / 77671362315038976000 : ℝ) ≤ (3303353656739 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (222593 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_409 : rowCell 6 409 ≤ (31964775300759 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1855112142768123 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3303353656739 / 1000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_409_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_409_1
  · norm_num [gridPoint]

theorem exp_6_410_0 : expNegUpper (10503411436750472029129 / 102549954006950656000 : ℝ) ≤ (3303353513052441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (222593 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_410_1 : expNegUpper (21030666900691148638079 / 205099908013901312000 : ℝ) ≤ (2940802486541709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_410 : rowCell 6 410 ≤ (56916183184289 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3303353513052441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2940802486541709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_410_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_410_1
  · norm_num [gridPoint]

theorem exp_6_411_0 : expNegUpper (400951867242447224650789 / 3910251227082056192000 : ℝ) ≤ (294080235949799 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (139247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_411_1 : expNegUpper (4014068511809021853889 / 39102512270820561920 : ℝ) ≤ (2617777703522043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2229979 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_411 : rowCell 6 411 ≤ (405336652232197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (294080235949799 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2617777703522043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_411_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_411_1
  · norm_num [gridPoint]

theorem exp_6_412_0 : expNegUpper (4027799454846792822689 / 39236270402057425920 : ℝ) ≤ (1308888795601751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2229979 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_412_1 : expNegUpper (403236880175754865638211 / 3923627040205742592000 : ℝ) ≤ (2330000522419421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279001 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_412 : rowCell 6 412 ≤ (360796425314783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1308888795601751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2330000522419421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_412_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_412_1
  · norm_num [gridPoint]

theorem exp_6_413_0 : expNegUpper (404613879315552756690299 / 3937025691635184128000 : ℝ) ≤ (116500021156407 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (279001 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_413_1 : expNegUpper (202536384045014255800249 / 1968512845817592064000 : ℝ) ≤ (20736518422761 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1117021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_413 : rowCell 6 413 ≤ (32111827959961 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (116500021156407 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20736518422761 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_413_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_413_1
  · norm_num [gridPoint]

theorem exp_6_414_0 : expNegUpper (8129073574548125892881 / 79008943627407616000 : ℝ) ≤ (518412938627217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1117021 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_414_1 : expNegUpper (16276580996642470800193 / 158017887254815232000 : ℝ) ≤ (230665407592713 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2236079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_414 : rowCell 6 414 ≤ (285775179066187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (518412938627217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (230665407592713 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_414_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_414_1
  · norm_num [gridPoint]

theorem exp_6_415_0 : expNegUpper (408299353712578542859217 / 3963891509411332608000 : ℝ) ≤ (922661591583913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2236079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_415_1 : expNegUpper (12773817520193540236883 / 123871609669104144000 : ℝ) ≤ (1641973263056471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2238119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_415 : rowCell 6 415 ≤ (254296789976577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (922661591583913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1641973263056471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_415_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_415_1
  · norm_num [gridPoint]

theorem sum_6_384_2 : blockSum (rowCell 6) 384 2 ≤ (8540889912723163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_384) (by simpa only [blockSum_one] using cell_6_385) (by norm_num)

theorem sum_6_386_2 : blockSum (rowCell 6) 386 2 ≤ (6805024765904601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_386) (by simpa only [blockSum_one] using cell_6_387) (by norm_num)

theorem sum_6_384_4 : blockSum (rowCell 6) 384 4 ≤ (3836478669656941 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_384_2 sum_6_386_2 (by norm_num)

theorem sum_6_388_2 : blockSum (rowCell 6) 388 2 ≤ (10838949944846253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_388) (by simpa only [blockSum_one] using cell_6_389) (by norm_num)

theorem sum_6_390_2 : blockSum (rowCell 6) 390 2 ≤ (8628151255264519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_390) (by simpa only [blockSum_one] using cell_6_391) (by norm_num)

theorem sum_6_388_4 : blockSum (rowCell 6) 388 4 ≤ (4866775300027693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_388_2 sum_6_390_2 (by norm_num)

theorem sum_6_384_8 : blockSum (rowCell 6) 384 8 ≤ (501589305573663 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_384_4 sum_6_388_4 (by norm_num)

theorem sum_6_392_2 : blockSum (rowCell 6) 392 2 ≤ (343260169910643 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_392) (by simpa only [blockSum_one] using cell_6_393) (by norm_num)

theorem sum_6_394_2 : blockSum (rowCell 6) 394 2 ≤ (2730022635339793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_394) (by simpa only [blockSum_one] using cell_6_395) (by norm_num)

theorem sum_6_392_4 : blockSum (rowCell 6) 392 4 ≤ (6162624334446223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_392_2 sum_6_394_2 (by norm_num)

theorem sum_6_396_2 : blockSum (rowCell 6) 396 2 ≤ (868117032540063 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_396) (by simpa only [blockSum_one] using cell_6_397) (by norm_num)

theorem sum_6_398_2 : blockSum (rowCell 6) 398 2 ≤ (1724572775828471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_398) (by simpa only [blockSum_one] using cell_6_399) (by norm_num)

theorem sum_6_396_4 : blockSum (rowCell 6) 396 4 ≤ (7789730714357257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_396_2 sum_6_398_2 (by norm_num)

theorem sum_6_392_8 : blockSum (rowCell 6) 392 8 ≤ (20114979383249703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_392_4 sum_6_396_4 (by norm_num)

theorem sum_6_384_16 : blockSum (rowCell 6) 384 16 ≤ (70273909940616003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_384_8 sum_6_392_8 (by norm_num)

theorem sum_6_400_2 : blockSum (rowCell 6) 400 2 ≤ (273960490562947 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_400) (by simpa only [blockSum_one] using cell_6_401) (by norm_num)

theorem sum_6_402_2 : blockSum (rowCell 6) 402 2 ≤ (1087550594734563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_402) (by simpa only [blockSum_one] using cell_6_403) (by norm_num)

theorem sum_6_400_4 : blockSum (rowCell 6) 400 4 ≤ (1228676523774649 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_400_2 sum_6_402_2 (by norm_num)

theorem sum_6_404_2 : blockSum (rowCell 6) 404 2 ≤ (1726187751724893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_404) (by simpa only [blockSum_one] using cell_6_405) (by norm_num)

theorem sum_6_406_2 : blockSum (rowCell 6) 406 2 ≤ (1369353323645771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_406) (by simpa only [blockSum_one] using cell_6_407) (by norm_num)

theorem sum_6_404_4 : blockSum (rowCell 6) 404 4 ≤ (386942634421333 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_404_2 sum_6_406_2 (by norm_num)

theorem sum_6_400_8 : blockSum (rowCell 6) 400 8 ≤ (400512358523463 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_400_4 sum_6_404_4 (by norm_num)

theorem sum_6_408_2 : blockSum (rowCell 6) 408 2 ≤ (542917453455471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_408) (by simpa only [blockSum_one] using cell_6_409) (by norm_num)

theorem sum_6_410_2 : blockSum (rowCell 6) 410 2 ≤ (860666117706509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_410) (by simpa only [blockSum_one] using cell_6_411) (by norm_num)

theorem sum_6_408_4 : blockSum (rowCell 6) 408 4 ≤ (1946501024617451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_408_2 sum_6_410_2 (by norm_num)

theorem sum_6_412_2 : blockSum (rowCell 6) 412 2 ≤ (681914704914393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_412) (by simpa only [blockSum_one] using cell_6_413) (by norm_num)

theorem sum_6_414_2 : blockSum (rowCell 6) 414 2 ≤ (135017992260691 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_414) (by simpa only [blockSum_one] using cell_6_415) (by norm_num)

theorem sum_6_412_4 : blockSum (rowCell 6) 412 4 ≤ (1221986673957157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_412_2 sum_6_414_2 (by norm_num)

theorem sum_6_408_8 : blockSum (rowCell 6) 408 8 ≤ (198030481160913 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_408_4 sum_6_412_4 (by norm_num)

theorem sum_6_400_16 : blockSum (rowCell 6) 400 16 ≤ (2794683717260967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_400_8 sum_6_408_8 (by norm_num)

theorem sum_6_384_32 : blockSum (rowCell 6) 384 32 ≤ (81452644809659871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_384_16 sum_6_400_16 (by norm_num)

#print axioms sum_6_384_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
