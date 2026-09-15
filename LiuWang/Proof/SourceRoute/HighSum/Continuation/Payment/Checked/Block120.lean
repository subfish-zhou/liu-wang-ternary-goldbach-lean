import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_256_0 : (31289667153187050540869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (71281663876472077629 / 825434552617984000 : ℝ) := by
  apply lower_of_taylor (t := (1963367 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_256 : (4563341281241465333861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 256 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (31289667153187050540869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_256_0
  · norm_num [gridPoint]

theorem exp_7_257_0 : (14283108717738354422933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9176188694939988311177 / 106147416521683968000 : ℝ) := by
  apply lower_of_taylor (t := (491191 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_257 : (1041537120177969397573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 257 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (14283108717738354422933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_257_0
  · norm_num [gridPoint]

theorem exp_7_258_0 : (1042928241468586397059 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (46142699178842990492513 / 533201761117768704000 : ℝ) := by
  apply lower_of_taylor (t := (983083 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_258 : (3802563218686563225331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 258 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1042928241468586397059 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_258_0
  · norm_num [gridPoint]

theorem exp_7_259_0 : (297397159244771097039 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4640553449145593817471 / 53567214920355635200 : ℝ) := by
  apply lower_of_taylor (t := (1967573 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_259 : (1734917443591117389609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 259 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (297397159244771097039 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_259_0
  · norm_num [gridPoint]

theorem exp_7_260_0 : (10852270144120727017683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (23334725955311723142371 / 269074123432891392000 : ℝ) := by
  apply lower_of_taylor (t := (393797 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_260 : (158271457799148204519 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 260 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (10852270144120727017683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_260_0
  · norm_num [gridPoint]

theorem exp_7_261_0 : (158364027753861504511 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (375475631475441412039 / 4325040432835584000 : ℝ) := by
  apply lower_of_taylor (t := (985201 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_261 : (2887011795998191504721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 261 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (158364027753861504511 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_261_0
  · norm_num [gridPoint]

theorem exp_7_262_0 : (9024962981528066558407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (377604344487686324139 / 4344940567356416000 : ℝ) := by
  apply lower_of_taylor (t := (1971823 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_262 : (526486727182564264049 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 262 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (9024962981528066558407 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_262_0
  · norm_num [gridPoint]

theorem exp_7_263_0 : (16454244470135684201821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (11866930447074987501127 / 136402699327773696000 : ℝ) := by
  apply lower_of_taylor (t := (7893 / 4000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_263 : (2399716579745120459051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 263 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (16454244470135684201821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_263_0
  · norm_num [gridPoint]

theorem exp_7_264_0 : (2999195928429703808599 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2386799630726615832427 / 27405486663953817600 : ℝ) := by
  apply lower_of_taylor (t := (1974681 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_264 : (43740812338237190057 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 264 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2999195928429703808599 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_264_0
  · norm_num [gridPoint]

theorem exp_7_265_0 : (6831826687969050726523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (48005358037742552131737 / 550614378823496704000 : ℝ) := by
  apply lower_of_taylor (t := (1976117 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_265 : (124545735013998287793 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 265 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6831826687969050726523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_265_0
  · norm_num [gridPoint]

theorem exp_7_266_0 : (6223356026175053560559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9655164111203063627273 / 110624946788871168000 : ℝ) := by
  apply lower_of_taylor (t := (1977557 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_266 : (907625425450229344571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 266 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (6223356026175053560559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_266_0
  · norm_num [gridPoint]

theorem exp_7_267_0 : (11335455326373187949043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (4854738266743527634469 / 55564079864165376000 : ℝ) := by
  apply lower_of_taylor (t := (1979003 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_267 : (165318317319455530731 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 267 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (11335455326373187949043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_267_0
  · norm_num [gridPoint]

theorem exp_7_268_0 : (10320970097937201276501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (24410023435043544219489 / 279081286457695232000 : ℝ) := by
  apply lower_of_taylor (t := (1980453 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_268 : (1505228824576306165073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 268 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (10320970097937201276501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_268_0
  · norm_num [gridPoint]

theorem exp_7_269_0 : (2348767328659540459341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (9818763132411083220299 / 112138011353113190400 : ℝ) := by
  apply lower_of_taylor (t := (495477 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_269 : (171274223826500532851 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 269 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2348767328659540459341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_269_0
  · norm_num [gridPoint]

theorem exp_7_270_0 : (8550235278542166047849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (49368691541424921014507 / 563223250192180224000 : ℝ) := by
  apply lower_of_taylor (t := (1983367 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_270 : (155872709590825703359 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 270 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8550235278542166047849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_270_0
  · norm_num [gridPoint]

theorem exp_7_271_0 : (7779567149093173335119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1241116925157006621507 / 14144053829880832000 : ℝ) := by
  apply lower_of_taylor (t := (1984831 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_271 : (1134586051933469425989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 271 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (7779567149093173335119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_271_0
  · norm_num [gridPoint]

theorem exp_7_272_0 : (3538366176518731770723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1248044363867652733027 / 14207669144368128000 : ℝ) := by
  apply lower_of_taylor (t := (19863 / 10000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_272 : (258020840592607636769 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 272 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3538366176518731770723 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_272_0
  · norm_num [gridPoint]

theorem exp_7_273_0 : (643592163020842383633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (50199986684787116079173 / 570857087930655744000 : ℝ) := by
  apply lower_of_taylor (t := (993887 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_273 : (938626375096275813051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 273 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (643592163020842383633 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_273_0
  · norm_num [gridPoint]

theorem exp_7_274_0 : (146295186525455299377 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2019172635784317872673 / 22936524786521006080 : ℝ) := by
  apply lower_of_taylor (t := (497313 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_274 : (170687623016285510309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 274 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (146295186525455299377 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_274_0
  · norm_num [gridPoint]

theorem exp_7_275_0 : (332469102350510222413 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (25379882341126631608151 / 287987430485916672000 : ℝ) := by
  apply lower_of_taylor (t := (398147 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_275 : (193951565168866787639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 275 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (332469102350510222413 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_275_0
  · norm_num [gridPoint]

theorem exp_7_276_0 : (2417269877924412072579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5104133554580772695987 / 57854231185708032000 : ℝ) := by
  apply lower_of_taylor (t := (996111 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_276 : (141015593011323260837 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 276 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2417269877924412072579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_276_0
  · norm_num [gridPoint]

theorem exp_7_277_0 : (1098202104946268634297 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10264806196671199945959 / 116223094463753216000 : ℝ) := by
  apply lower_of_taylor (t := (996857 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_277 : (640655073269084571809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 277 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1098202104946268634297 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_277_0
  · norm_num [gridPoint]

theorem exp_7_278_0 : (1995277481862114684677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (51607853492982743208343 / 583694342356890624000 : ℝ) := by
  apply lower_of_taylor (t := (199521 / 100000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_278 : (581989706437992053201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 278 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1995277481862114684677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_278_0
  · norm_num [gridPoint]

theorem exp_7_279_0 : (3624339509997623271677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2594640278638630953889 / 29313946098572697600 : ℝ) := by
  apply lower_of_taylor (t := (1996711 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_279 : (13214504665577760123 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 279 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3624339509997623271677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_279_0
  · norm_num [gridPoint]

theorem exp_7_280_0 : (3291013192521407538533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13044722430202572255093 / 147217302790614016000 : ℝ) := by
  apply lower_of_taylor (t := (1998217 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_280 : (479967277536652387323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 280 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (3291013192521407538533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_280_0
  · norm_num [gridPoint]

theorem exp_7_281_0 : (746923596918050045433 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (10493221687036082943677 / 118293041985979392000 : ℝ) := by
  apply lower_of_taylor (t := (1999727 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_281 : (108932679502866630747 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 281 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (746923596918050045433 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_281_0
  · norm_num [gridPoint]

theorem exp_7_282_0 : (677936701177409413463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (340351382025597792607 / 3832689795314688000 : ℝ) := by
  apply lower_of_taylor (t := (2001241 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_282 : (395486026668893268067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 282 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (677936701177409413463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_282_0
  · norm_num [gridPoint]

theorem exp_7_283_0 : (15379745612825325789 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (855547734762204517899 / 9623779616033792000 : ℝ) := by
  apply lower_of_taylor (t := (50069 / 25000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_283 : (89720389426193742343 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 283 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (15379745612825325789 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_283_0
  · norm_num [gridPoint]

theorem exp_7_284_0 : (44650545463482621693 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (5333459695713214316761 / 59928746369085235200 : ℝ) := by
  apply lower_of_taylor (t := (501071 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_284 : (40699473636519907769 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 284 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (44650545463482621693 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_284_0
  · norm_num [gridPoint]

theorem exp_7_285_0 : (2025035566776504359283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (53626378917678708709967 / 601906300764048384000 : ℝ) := by
  apply lower_of_taylor (t := (501453 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_285 : (295334825794469447289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 285 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (2025035566776504359283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_285_0
  · norm_num [gridPoint]

theorem exp_7_286_0 : (1836442690205980948333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2156772317399241536763 / 24181233896547328000 : ℝ) := by
  apply lower_of_taylor (t := (125459 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_286 : (8369690681174975793 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 286 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (1836442690205980948333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_286_0
  · norm_num [gridPoint]

theorem exp_7_287_0 : (83253316645501538151 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (135533466267809484943 / 1517902759099392000 : ℝ) := by
  apply lower_of_taylor (t := (2008881 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_287 : (24283626590766583419 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 287 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (83253316645501538151 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_287_0
  · norm_num [gridPoint]

theorem sum_7_256_2 : (8729489761953342924153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_256) (by simpa only [blockSum_one] using cell_7_257) (by norm_num)

theorem sum_7_258_2 : (7272398105868798004549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 258 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_258) (by simpa only [blockSum_one] using cell_7_259) (by norm_num)

theorem sum_7_256_4 : (8000943933911070464351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_256_2 sum_7_258_2 (by norm_num)

theorem sum_7_260_2 : (6052440951981155595101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 260 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_260) (by simpa only [blockSum_one] using cell_7_261) (by norm_num)

theorem sum_7_262_2 : (157254694239310680603 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 262 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_262) (by simpa only [blockSum_one] using cell_7_263) (by norm_num)

theorem sum_7_260_4 : (11084591167639097374397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 260 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_260_2 sum_7_262_2 (by norm_num)

theorem sum_7_256_8 : (27086479035461238303099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_256_4 sum_7_260_4 (by norm_num)

theorem sum_7_264_2 : (2089886188567916053769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 264 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_264) (by simpa only [blockSum_one] using cell_7_265) (by norm_num)

theorem sum_7_266_2 : (867108506023753499113 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 266 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_266) (by simpa only [blockSum_one] using cell_7_267) (by norm_num)

theorem sum_7_264_4 : (764820640123084610399 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 264 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_264_2 sum_7_266_2 (by norm_num)

theorem sum_7_268_2 : (2875422615188310427881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 268 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_268) (by simpa only [blockSum_one] using cell_7_269) (by norm_num)

theorem sum_7_270_2 : (2381567728660075052861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 270 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_270) (by simpa only [blockSum_one] using cell_7_271) (by norm_num)

theorem sum_7_268_4 : (2628495171924192740371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 268 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_268_2 sum_7_270_2 (by norm_num)

theorem sum_7_264_8 : (3226299186269807896183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 264 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_264_4 sum_7_268_4 (by norm_num)

theorem sum_7_256_16 : (39991675780540469887831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_256_8 sum_7_264_8 (by norm_num)

theorem sum_7_272_2 : (1970709737466706360127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 272 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_272) (by simpa only [blockSum_one] using cell_7_273) (by norm_num)

theorem sum_7_274_2 : (1629244375756894702101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 274 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_274) (by simpa only [blockSum_one] using cell_7_275) (by norm_num)

theorem sum_7_272_4 : (899988528305900265557 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 272 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_272_2 sum_7_274_2 (by norm_num)

theorem sum_7_276_2 : (672866519162850437997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 276 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_276) (by simpa only [blockSum_one] using cell_7_277) (by norm_num)

theorem sum_7_278_2 : (1110569893061102458121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 278 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_278) (by simpa only [blockSum_one] using cell_7_279) (by norm_num)

theorem sum_7_276_4 : (491260586277360666823 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 276 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_276_2 sum_7_278_2 (by norm_num)

theorem sum_7_272_8 : (6056257044610404396343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 272 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_272_4 sum_7_276_4 (by norm_num)

theorem sum_7_280_2 : (915697995548118910311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 280 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_280) (by simpa only [blockSum_one] using cell_7_281) (by norm_num)

theorem sum_7_282_2 : (754367584373668237439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 282 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_282) (by simpa only [blockSum_one] using cell_7_283) (by norm_num)

theorem sum_7_280_4 : (6680262319687148591 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 280 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_280_2 sum_7_282_2 (by norm_num)

theorem sum_7_284_2 : (620930614886628709441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 284 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_284) (by simpa only [blockSum_one] using cell_7_285) (by norm_num)

theorem sum_7_286_2 : (255333183852632529783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 286 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_286) (by simpa only [blockSum_one] using cell_7_287) (by norm_num)

theorem sum_7_284_4 : (1131596982591893769007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 284 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_284_2 sum_7_286_2 (by norm_num)

theorem sum_7_280_8 : (2801662562513680916757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 280 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_280_4 sum_7_284_4 (by norm_num)

theorem sum_7_272_16 : (88579196071240853131 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 272 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_272_8 sum_7_280_8 (by norm_num)

theorem sum_7_256_32 : (48849595387664555200931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 256 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_256_16 sum_7_272_16 (by norm_num)

#print axioms sum_7_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
