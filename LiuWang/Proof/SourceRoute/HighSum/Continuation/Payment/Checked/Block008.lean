import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_256_0 : expNegUpper (73806424076024574441 / 917150741966258000 : ℝ) ≤ (5625519773849768187218401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_256_1 : expNegUpper (3783795573179093656491 / 46958117988672409600 : ℝ) ≤ (10134752762000122401436859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938351 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_256 : rowCell 0 256 ≤ (1559471189021077363723889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5625519773849768187218401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10134752762000122401436859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_256_1
  · norm_num [gridPoint]

theorem exp_0_257_0 : expNegUpper (34212671426663640600859 / 424590237044379750400 : ℝ) ≤ (10134751634880795852882811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938351 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_257_1 : expNegUpper (85642795668503669831943 / 1061475592610949376000 : ℝ) ≤ (228186749022498696101853 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_257 : rowCell 0 257 ≤ (280923700933309357928803 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10134751634880795852882811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (228186749022498696101853 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_257_1
  · norm_num [gridPoint]

theorem exp_0_258_0 : expNegUpper (86040509985813480147447 / 1066404949629647104000 : ℝ) ≤ (9127468955177371235542393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_258_1 : expNegUpper (172304691987886187493733 / 2132809899259294208000 : ℝ) ≤ (1027342018865331572472583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_258 : rowCell 0 258 ≤ (39528151900561367136047 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9127468955177371235542393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1027342018865331572472583 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_258_1
  · norm_num [gridPoint]

theorem exp_0_259_0 : expNegUpper (769346664793002391613 / 9523073118233088000 : ℝ) ≤ (4109367626836605404767349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879777 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_259_1 : expNegUpper (192586791931149338623 / 2380768279558272000 : ℝ) ≤ (1849769510901154091371671 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_259 : rowCell 0 259 ≤ (284716244316658357662603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4109367626836605404767349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1849769510901154091371671 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_259_1
  · norm_num [gridPoint]

theorem exp_0_260_0 : expNegUpper (43532326486513145796863 / 538148960562837632000 : ℝ) ≤ (3699538621631483853827699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_260_1 : expNegUpper (174355863579790638193851 / 2152595842251350528000 : ℝ) ≤ (6659915027158887560846121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470717 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_260 : rowCell 0 260 ≤ (256298586871257410828681 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3699538621631483853827699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6659915027158887560846121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_260_1
  · norm_num [gridPoint]

theorem exp_0_261_0 : expNegUpper (175159949066846742247539 / 2162523071206011392000 : ℝ) ≤ (6659914313377227171020383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470717 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_261_1 : expNegUpper (701551818021974138089 / 8650092284824045568 : ℝ) ≤ (5993476947922119859906249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94221 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_261 : rowCell 0 261 ≤ (922696659055159709127269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6659914313377227171020383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5993476947922119859906249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_261_1
  · norm_num [gridPoint]

theorem exp_0_262_0 : expNegUpper (78308861748065183121 / 965543617096189952 : ℝ) ≤ (5993476311443795121542393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94221 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_262_1 : expNegUpper (19602710611942415608329 / 241385904274047488000 : ℝ) ≤ (2696364632821294995639813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75439 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_262 : rowCell 0 262 ≤ (830292340475212365976107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5993476311443795121542393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2696364632821294995639813 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_262_1
  · norm_num [gridPoint]

theorem exp_0_263_0 : expNegUpper (177234285537290989240649 / 2182446044032598528000 : ℝ) ≤ (5392728698188630268268323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (75439 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_263_1 : expNegUpper (22183149572261737847631 / 272805755504074816000 : ℝ) ≤ (2425652470938284411199117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377507 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_263 : rowCell 0 263 ≤ (373502068328763906884357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5392728698188630268268323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2425652470938284411199117 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_263_1
  · norm_num [gridPoint]

theorem exp_0_264_0 : expNegUpper (891389994358091853159 / 10962208939522624000 : ℝ) ≤ (485130443604383321531639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377507 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_264_1 : expNegUpper (7140414708386746726783 / 87697671516180992000 : ℝ) ≤ (4363442474321640326527199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_264 : rowCell 0 264 ≤ (67194762357802761215137 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (485130443604383321531639 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4363442474321640326527199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_264_1
  · norm_num [gridPoint]

theorem exp_0_265_0 : expNegUpper (19925120992051939213863 / 244717818898022912000 : ℝ) ≤ (2181721011745707276302189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_265_1 : expNegUpper (9975551049696926853867 / 122358909449011456000 : ℝ) ≤ (784785907842904930540319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945333 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_265 : rowCell 0 265 ≤ (604322580037905455468167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2181721011745707276302189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (784785907842904930540319 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_265_1
  · norm_num [gridPoint]

theorem exp_0_266_0 : expNegUpper (90189282850088441424307 / 1106250895282821376000 : ℝ) ≤ (1961964568735256720131353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (945333 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_266_1 : expNegUpper (36122772025012119022041 / 442500358113128550400 : ℝ) ≤ (3528051749275013647765103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (946119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_266 : rowCell 0 266 ≤ (543405141400561770693481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1961964568735256720131353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3528051749275013647765103 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_266_1
  · norm_num [gridPoint]

theorem exp_0_267_0 : expNegUpper (1170551220510227787951 / 14339135802289254400 : ℝ) ≤ (3528051391329779199582241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (946119 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_267_1 : expNegUpper (1465098398335121371939 / 17923919752861568000 : ℝ) ≤ (99110814886961717921359 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1893813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_267 : rowCell 0 267 ≤ (488540666515199348297843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3528051391329779199582241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99110814886961717921359 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_267_1
  · norm_num [gridPoint]

theorem exp_0_268_0 : expNegUpper (5069353315486982569589 / 62018142956938368000 : ℝ) ≤ (3171545757511766151410851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1893813 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_268_1 : expNegUpper (20303883632485188347707 / 248072571827753472000 : ℝ) ≤ (1425279263252904238153573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59231 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_268 : rowCell 0 268 ≤ (439137254874879213892901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3171545757511766151410851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1425279263252904238153573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_268_1
  · norm_num [gridPoint]

theorem exp_0_269_0 : expNegUpper (7342496649114149027843 / 89710523274019328000 : ℝ) ≤ (114022329699528413546687 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (59231 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_269_1 : expNegUpper (3676042480276683537321 / 44855261637009664000 : ℝ) ≤ (512321137922997283797977 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (118561 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_269 : rowCell 0 269 ≤ (39465985641999785653419 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (114022329699528413546687 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (512321137922997283797977 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_269_1
  · norm_num [gridPoint]

theorem exp_0_270_0 : expNegUpper (92316269891195506717041 / 1126447927778470144000 : ℝ) ≤ (2561605436680696463082043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (118561 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_270_1 : expNegUpper (184873725350296142059561 / 2252895855556940288000 : ℝ) ≤ (1150769909828602967336817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898563 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_270 : rowCell 0 270 ≤ (35462492132422608392853 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2561605436680696463082043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1150769909828602967336817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_270_1
  · norm_num [gridPoint]

theorem exp_0_271_0 : expNegUpper (20634122223720209160921 / 251450163063239168000 : ℝ) ≤ (1150769797219656320728929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898563 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_271_1 : expNegUpper (258263564852904496443 / 3143127038290489600 : ℝ) ≤ (1033758564671113442978327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950077 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_271 : rowCell 0 271 ≤ (159297770811275067407993 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1150769797219656320728929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1033758564671113442978327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_271_1
  · norm_num [gridPoint]

theorem exp_0_272_0 : expNegUpper (2334826336418312243347 / 28415373973588998400 : ℝ) ≤ (2067516928834428642618193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950077 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_272_1 : expNegUpper (187030258037558109733311 / 2273229917887119872000 : ℝ) ≤ (1856969011731466683161083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1901749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_272 : rowCell 0 272 ≤ (286177040691402314327407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2067516928834428642618193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1856969011731466683161083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_272_1
  · norm_num [gridPoint]

theorem exp_0_273_0 : expNegUpper (187869570474678951221559 / 2283431206510842368000 : ℝ) ≤ (1856968833249925516654467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1901749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_273_1 : expNegUpper (94057604686517702835839 / 1141715603255421184000 : ℝ) ≤ (333515185118454933158857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_273 : rowCell 0 273 ≤ (25701297039795500959339 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1856968833249925516654467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (333515185118454933158857 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_273_1
  · norm_num [gridPoint]

theorem exp_0_274_0 : expNegUpper (16796222283507772839 / 203880474083584000 : ℝ) ≤ (833787883370725020862791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_274_1 : expNegUpper (33636378789842092797 / 407760948167168000 : ℝ) ≤ (748621852188022571635159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_274 : rowCell 0 274 ≤ (115390739613190665507241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (833787883370725020862791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (748621852188022571635159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_274_1
  · norm_num [gridPoint]

theorem exp_0_275_0 : expNegUpper (190049907550154105848397 / 2303902298675552768000 : ℝ) ≤ (1497243563018098900428743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1904951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_275_1 : expNegUpper (47574632997343963849179 / 575975574668888192000 : ℝ) ≤ (336020517414377431228437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_275 : rowCell 0 275 ≤ (207192017888203487952099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1497243563018098900428743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (336020517414377431228437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_275_1
  · norm_num [gridPoint]

theorem exp_0_276_0 : expNegUpper (47786700262273145544891 / 578543025554135168000 : ℝ) ≤ (84005121492807156735973 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_276_1 : expNegUpper (38279384650983260528303 / 462834420443308134400 : ℝ) ≤ (1206385149088109876172133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238521 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_276 : rowCell 0 276 ≤ (92991175927435890514531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (84005121492807156735973 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1206385149088109876172133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_276_1
  · norm_num [gridPoint]

theorem exp_0_277_0 : expNegUpper (4272182026191478225807 / 51654772090295193600 : ℝ) ≤ (301596259299782658034413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (238521 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_277_1 : expNegUpper (10694434137878986691477 / 129136930225737984000 : ℝ) ≤ (1082613816509600038052677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_277 : rowCell 0 277 ≤ (166915852934848269407991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (301596259299782658034413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1082613816509600038052677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_277_1
  · norm_num [gridPoint]

theorem exp_0_278_0 : expNegUpper (96677043965532283261357 / 1167390112107890944000 : ℝ) ≤ (541306858493175829234007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1909783 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_278_1 : expNegUpper (193607215662430875540993 / 2334780224215781888000 : ℝ) ≤ (485689843987757940714953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_278 : rowCell 0 278 ≤ (5991161778980766057489 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (541306858493175829234007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (485689843987757940714953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_278_1
  · norm_num [gridPoint]

theorem exp_0_279_0 : expNegUpper (7778580051951014719713 / 93804741706961408000 : ℝ) ≤ (971379599464330243790943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911401 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_279_1 : expNegUpper (973595683945411473269 / 11725592713370176000 : ℝ) ≤ (54464413884909939785013 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_279 : rowCell 0 279 ≤ (67189688505274787818897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (971379599464330243790943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54464413884909939785013 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_279_1
  · norm_num [gridPoint]

theorem exp_0_280_0 : expNegUpper (2716381128806771823621 / 32714995825528384000 : ℝ) ≤ (27232204482888183564477 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1913023 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_280_1 : expNegUpper (21759509761568296057119 / 261719966604227072000 : ℝ) ≤ (781637587092824263586307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_280 : rowCell 0 280 ≤ (3766975414304933909437 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27232204482888183564477 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (781637587092824263586307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_280_1
  · norm_num [gridPoint]

theorem exp_0_281_0 : expNegUpper (196698917849339823175439 / 2365863694507807232000 : ℝ) ≤ (156327503423133348200943 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1914649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_281_1 : expNegUpper (19695657884986663185087 / 236586369450780723200 : ℝ) ≤ (700982767514116742847183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1916279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_281 : rowCell 0 281 ≤ (5405700159843289185679 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156327503423133348200943 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (700982767514116742847183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_281_1
  · norm_num [gridPoint]

theorem exp_0_282_0 : expNegUpper (19782294101687077034607 / 237627052788332595200 : ℝ) ≤ (700982705306768620282859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1916279 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_282_1 : expNegUpper (198082119768676843393261 / 2376270527883325952000 : ℝ) ≤ (628548798314427548947727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239739 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_282 : rowCell 0 282 ≤ (12118828968127238666091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (700982705306768620282859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (628548798314427548947727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_282_1
  · norm_num [gridPoint]

theorem exp_0_283_0 : expNegUpper (22105724529891006615741 / 265188911062733312000 : ℝ) ≤ (314274371511029303847489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239739 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_283_1 : expNegUpper (5533672794524554051953 / 66297227765683328000 : ℝ) ≤ (563509019905630546035443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38391 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_283 : rowCell 0 283 ≤ (86925923062083473435747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (314274371511029303847489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (563509019905630546035443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_283_1
  · norm_num [gridPoint]

theorem exp_0_284_0 : expNegUpper (2000846670981233374913 / 23971527095516288000 : ℝ) ≤ (281754485383262375481983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (38391 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_284_1 : expNegUpper (8013875653793063440443 / 95886108382065152000 : ℝ) ≤ (252559330336731024831107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1921191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_284 : rowCell 0 284 ≤ (77925286979741459364803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (281754485383262375481983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (252559330336731024831107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_284_1
  · norm_num [gridPoint]

theorem exp_0_285_0 : expNegUpper (201222389996522250924027 / 2407628057844412928000 : ℝ) ≤ (505118617008984926677329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1921191 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_285_1 : expNegUpper (100743070993421705272313 / 1203814028922206464000 : ℝ) ≤ (28294178766895014201589 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480709 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_285 : rowCell 0 285 ≤ (69845494349534174948313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (505118617008984926677329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28294178766895014201589 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_285_1
  · norm_num [gridPoint]

theorem exp_0_286_0 : expNegUpper (11242483303141913698273 / 134340346913497344000 : ℝ) ≤ (90541364295190864015437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (480709 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_286_1 : expNegUpper (900577700094546960889 / 10747227753079787520 : ℝ) ≤ (16226778212518331062979 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384897 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_286 : rowCell 0 286 ≤ (62593569300883684086501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90541364295190864015437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16226778212518331062979 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_286_1
  · norm_num [gridPoint]

theorem exp_0_287_0 : expNegUpper (8140464218822342846201 / 97145890773889863680 : ℝ) ≤ (81133884170058894999241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (384897 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_287_1 : expNegUpper (6368075716889193740823 / 75895227167101456000 : ℝ) ≤ (181731228090935072782479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1926137 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_287 : rowCell 0 287 ≤ (28042893745053107608361 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (81133884170058894999241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (181731228090935072782479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_287_1
  · norm_num [gridPoint]

theorem sum_0_256_2 : blockSum (rowCell 0) 256 2 ≤ (92627802927738254792747 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_256) (by simpa only [blockSum_one] using cell_0_257) (by norm_num)

theorem sum_0_258_2 : blockSum (rowCell 0) 258 2 ≤ (600941459521149294750979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_258) (by simpa only [blockSum_one] using cell_0_259) (by norm_num)

theorem sum_0_256_4 : blockSum (rowCell 0) 256 4 ≤ (268392776588611066618591 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_256_2 sum_0_258_2 (by norm_num)

theorem sum_0_260_2 : blockSum (rowCell 0) 260 2 ≤ (1947891006540189352441993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_260) (by simpa only [blockSum_one] using cell_0_261) (by norm_num)

theorem sum_0_262_2 : blockSum (rowCell 0) 262 2 ≤ (1577296477132740179744821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_262) (by simpa only [blockSum_one] using cell_0_263) (by norm_num)

theorem sum_0_260_4 : blockSum (rowCell 0) 260 4 ≤ (1762593741836464766093407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_260_2 sum_0_262_2 (by norm_num)

theorem sum_0_256_8 : blockSum (rowCell 0) 256 8 ≤ (4446521507722575432279317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_256_4 sum_0_260_4 (by norm_num)

theorem sum_0_264_2 : blockSum (rowCell 0) 264 2 ≤ (1276270203615933067619537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_264) (by simpa only [blockSum_one] using cell_0_265) (by norm_num)

theorem sum_0_266_2 : blockSum (rowCell 0) 266 2 ≤ (257986451978940279747831 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_266) (by simpa only [blockSum_one] using cell_0_267) (by norm_num)

theorem sum_0_264_4 : blockSum (rowCell 0) 264 4 ≤ (2308216011531694186610861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_264_2 sum_0_266_2 (by norm_num)

theorem sum_0_268_2 : blockSum (rowCell 0) 268 2 ≤ (833797111294877070427091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_268) (by simpa only [blockSum_one] using cell_0_269) (by norm_num)

theorem sum_0_270_2 : blockSum (rowCell 0) 270 2 ≤ (168305115736694054686129 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_270) (by simpa only [blockSum_one] using cell_0_271) (by norm_num)

theorem sum_0_268_4 : blockSum (rowCell 0) 268 4 ≤ (1507017574241653289171607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_268_2 sum_0_270_2 (by norm_num)

theorem sum_0_264_8 : blockSum (rowCell 0) 264 8 ≤ (953808396443336868945617 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_264_4 sum_0_268_4 (by norm_num)

theorem sum_0_256_16 : blockSum (rowCell 0) 256 16 ≤ (6354138300609249170170551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_256_8 sum_0_264_8 (by norm_num)

theorem sum_0_272_2 : blockSum (rowCell 0) 272 2 ≤ (543190011089357323920797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_272) (by simpa only [blockSum_one] using cell_0_273) (by norm_num)

theorem sum_0_274_2 : blockSum (rowCell 0) 274 2 ≤ (437973497114584818966581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_274) (by simpa only [blockSum_one] using cell_0_275) (by norm_num)

theorem sum_0_272_4 : blockSum (rowCell 0) 272 4 ≤ (490581754101971071443689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_272_2 sum_0_274_2 (by norm_num)

theorem sum_0_276_2 : blockSum (rowCell 0) 276 2 ≤ (352898204789720050437053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_276) (by simpa only [blockSum_one] using cell_0_277) (by norm_num)

theorem sum_0_278_2 : blockSum (rowCell 0) 278 2 ≤ (284158421485068727075019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_278) (by simpa only [blockSum_one] using cell_0_279) (by norm_num)

theorem sum_0_276_4 : blockSum (rowCell 0) 276 4 ≤ (79632078284348597189009 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_276_2 sum_0_278_2 (by norm_num)

theorem sum_0_272_8 : blockSum (rowCell 0) 272 8 ≤ (32364402689574618407989 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_272_4 sum_0_276_4 (by norm_num)

theorem sum_0_280_2 : blockSum (rowCell 0) 280 2 ≤ (57164304113655917203891 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_280) (by simpa only [blockSum_one] using cell_0_281) (by norm_num)

theorem sum_0_282_2 : blockSum (rowCell 0) 282 2 ≤ (7355062192284055310579 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_282) (by simpa only [blockSum_one] using cell_0_283) (by norm_num)

theorem sum_0_280_4 : blockSum (rowCell 0) 280 4 ≤ (412533771261725051580039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_280_2 sum_0_282_2 (by norm_num)

theorem sum_0_284_2 : blockSum (rowCell 0) 284 2 ≤ (36942695332318908578279 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_284) (by simpa only [blockSum_one] using cell_0_285) (by norm_num)

theorem sum_0_286_2 : blockSum (rowCell 0) 286 2 ≤ (118679356790989899303223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_286) (by simpa only [blockSum_one] using cell_0_287) (by norm_num)

theorem sum_0_284_4 : blockSum (rowCell 0) 284 4 ≤ (266450138120265533616339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_284_2 sum_0_286_2 (by norm_num)

theorem sum_0_280_8 : blockSum (rowCell 0) 280 8 ≤ (339491954690995292598189 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_280_4 sum_0_284_4 (by norm_num)

theorem sum_0_272_16 : blockSum (rowCell 0) 272 16 ≤ (574301010965180376398957 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_272_8 sum_0_280_8 (by norm_num)

theorem sum_0_256_32 : blockSum (rowCell 0) 256 32 ≤ (1500548064507921984593693 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_256_16 sum_0_272_16 (by norm_num)

#print axioms sum_0_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
