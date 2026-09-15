import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_288_0 : expNegUpper (6606289483978005731607 / 76224722892415504000 : ℝ) ≤ (22947870400711904511497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (984079 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_288_1 : expNegUpper (211655055224508113792623 / 2439191132557296128000 : ℝ) ≤ (10340109505792370136279 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_288 : rowCell 2 288 ≤ (3181399477056252697921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22947870400711904511497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10340109505792370136279 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_288_1
  · norm_num [gridPoint]

theorem exp_2_289_0 : expNegUpper (2834292747398671494229 / 32663437787641344000 : ℝ) ≤ (20680216997151488965497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1969759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_289_1 : expNegUpper (1418848592392322661253 / 16331718893820672000 : ℝ) ≤ (9316645033160130737403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_289 : rowCell 2 289 ≤ (358347031974670297501 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20680216997151488965497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9316645033160130737403 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_289_1
  · norm_num [gridPoint]

theorem exp_2_290_0 : expNegUpper (106873637576746204925671 / 1230173686947330304000 : ℝ) ≤ (2329161033360381817963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971363 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_290_1 : expNegUpper (214004152354956102621381 / 2460347373894660608000 : ℝ) ≤ (8392979720910585001183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (493243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_290 : rowCell 2 290 ≤ (645700841224768835713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2329161033360381817963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8392979720910585001183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_290_1
  · norm_num [gridPoint]

theorem exp_2_291_0 : expNegUpper (214927230775410973492989 / 2470959752021975552000 : ℝ) ≤ (8392978917345961276453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (493243 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_291_1 : expNegUpper (10759282785258493541099 / 123547987601098777600 : ℝ) ≤ (15119085013621205780583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (394917 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_291 : rowCell 2 291 ≤ (465308877837185469881 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8392978917345961276453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15119085013621205780583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_291_1
  · norm_num [gridPoint]

theorem exp_2_292_0 : expNegUpper (514551983126177856479 / 5908559448702489600 : ℝ) ≤ (7559541789238282447161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (394917 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_292_1 : expNegUpper (10303419471515635738991 / 118171188974049792000 : ℝ) ≤ (3403831625495028056357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_292 : rowCell 2 292 ≤ (2095338999138457555869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7559541789238282447161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3403831625495028056357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_292_1
  · norm_num [gridPoint]

theorem exp_2_293_0 : expNegUpper (217301091558582235264979 / 2492253023193870848000 : ℝ) ≤ (13615325220618334435039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1976201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_293_1 : expNegUpper (108781310968635094220469 / 1246126511596935424000 : ℝ) ≤ (766186213849394855229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_293 : rowCell 2 293 ≤ (7370224769357155847 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13615325220618334435039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (766186213849394855229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_293_1
  · norm_num [gridPoint]

theorem exp_2_294_0 : expNegUpper (4369900334090244537069 / 50058678324769024000 : ℝ) ≤ (12258978277712764945803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988911 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_294_1 : expNegUpper (8750324192153361252697 / 100117356649538048000 : ℝ) ≤ (2758955991174190116399 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_294 : rowCell 2 294 ≤ (106167369277524516113 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12258978277712764945803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2758955991174190116399 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_294_1
  · norm_num [gridPoint]

theorem exp_2_295_0 : expNegUpper (73231206114374440405219 / 837879215862928896000 : ℝ) ≤ (11035822943711563976359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1979447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_295_1 : expNegUpper (9164927812244105244889 / 104734901982866112000 : ℝ) ≤ (4966493756266528073133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495269 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_295 : rowCell 2 295 ≤ (764532248817500990809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11035822943711563976359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4966493756266528073133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_295_1
  · norm_num [gridPoint]

theorem exp_2_296_0 : expNegUpper (27612113308344270635083 / 315545527155609664000 : ℝ) ≤ (2483246650344684153227 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495269 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_296_1 : expNegUpper (44232623999936463769947 / 504872843448975462400 : ℝ) ≤ (8938819580180015925563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_296 : rowCell 2 296 ≤ (688074530948815239649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2483246650344684153227 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8938819580180015925563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_296_1
  · norm_num [gridPoint]

theorem exp_2_297_0 : expNegUpper (44420978213548681035507 / 507022725041344614400 : ℝ) ≤ (4469409383583532665607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_297_1 : expNegUpper (111186336156822028481843 / 1267556812603361536000 : ℝ) ≤ (100534726265476819101 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992173 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_297 : rowCell 2 297 ≤ (1238313300547544433667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4469409383583532665607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (100534726265476819101 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_297_1
  · norm_num [gridPoint]

theorem exp_2_298_0 : expNegUpper (1200632162034568216319 / 13687558448786688000 : ℝ) ≤ (502673585994173195543 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992173 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_298_1 : expNegUpper (2404160585248197709121 / 27375116897573376000 : ℝ) ≤ (1447065210351382952251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992993 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_298 : rowCell 2 298 ≤ (17407703568223191667 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (502673585994173195543 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1447065210351382952251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_298_1
  · norm_num [gridPoint]

theorem exp_2_299_0 : expNegUpper (51322283353406093939 / 584384218525184000 : ℝ) ≤ (11576520647598916751 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992993 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_299_1 : expNegUpper (12846052362019197459 / 146096054631296000 : ℝ) ≤ (1626959374578652171653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1987631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_299 : rowCell 2 299 ≤ (3914702290095088351 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11576520647598916751 / 1600000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1626959374578652171653 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_299_1
  · norm_num [gridPoint]

theorem exp_2_300_0 : expNegUpper (56439280914561992537493 / 641874719731697792000 : ℝ) ≤ (6507836921260366383641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1987631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_300_1 : expNegUpper (226029628027743409445491 / 2567498878926791168000 : ℝ) ≤ (5852512233582410133269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12433 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_300 : rowCell 2 300 ≤ (901327765372329067671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6507836921260366383641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5852512233582410133269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_300_1
  · norm_num [gridPoint]

theorem exp_2_301_0 : expNegUpper (75661331364019087488313 / 859446546703885824000 : ℝ) ≤ (2926255859497782704451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12433 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_301_1 : expNegUpper (7575269316588113180543 / 85944654670388582400 : ℝ) ≤ (5262298234681509467073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_301 : rowCell 2 301 ≤ (6332046310814062943 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2926255859497782704451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5262298234681509467073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_301_1
  · norm_num [gridPoint]

theorem exp_2_302_0 : expNegUpper (22821561096491818465709 / 258920323960227891200 : ℝ) ≤ (5262297775868284265399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_302_1 : expNegUpper (228491280737374560173961 / 2589203239602278912000 : ℝ) ≤ (295676327853703596651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (199259 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_302 : rowCell 2 302 ≤ (728707217242659252569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5262297775868284265399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (295676327853703596651 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_302_1
  · norm_num [gridPoint]

theorem exp_2_303_0 : expNegUpper (229451984269169383455489 / 2600089677398655488000 : ℝ) ≤ (591352604579405315279 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (199259 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_303_1 : expNegUpper (14358077608704721902973 / 162505604837415968000 : ℝ) ≤ (4252320845939315041373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7977 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_303 : rowCell 2 303 ≤ (327529381142346087809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (591352604579405315279 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4252320845939315041373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_303_1
  · norm_num [gridPoint]

theorem exp_2_304_0 : expNegUpper (192244269997624587991 / 2175832461250656000 : ℝ) ≤ (2126160240677601648471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7977 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_304_1 : expNegUpper (3079626299942466839549 / 34813319380010496000 : ℝ) ≤ (3821592422076385168583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (399183 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_304 : rowCell 2 304 ≤ (147189245706088901931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2126160240677601648471 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3821592422076385168583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_304_1
  · norm_num [gridPoint]

theorem exp_2_305_0 : expNegUpper (231939040141197197787287 / 2621931067908674048000 : ℝ) ≤ (95539802428784438467 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (399183 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_305_1 : expNegUpper (116109741499470797229423 / 1310965533954337024000 : ℝ) ≤ (1716967255485542696223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_305 : rowCell 2 305 ≤ (529079518901476981963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (95539802428784438467 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1716967255485542696223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_305_1
  · norm_num [gridPoint]

theorem exp_2_306_0 : expNegUpper (16656410192403650484201 / 188063287187308288000 : ℝ) ≤ (3433934221433186562123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1997583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_306_1 : expNegUpper (6670622378325255475847 / 75225314874923315200 : ℝ) ≤ (3085101029247304238153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249907 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_306 : rowCell 2 306 ≤ (47537390742535442241 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3433934221433186562123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3085101029247304238153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_306_1
  · norm_num [gridPoint]

theorem exp_2_307_0 : expNegUpper (15629682776456658619523 / 176257587442780876800 : ℝ) ≤ (385637596409975888667 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (249907 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_307_1 : expNegUpper (19560740267945891773553 / 220321984303476096000 : ℝ) ≤ (4434012713771845037 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (500233 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_307 : rowCell 2 307 ≤ (213525469622080262273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (385637596409975888667 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4434012713771845037 / 1600000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_307_1
  · norm_num [gridPoint]

theorem exp_2_308_0 : expNegUpper (58926386748283040514611 / 663716110241716352000 : ℝ) ≤ (277125771630092933101 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (500233 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_308_1 : expNegUpper (235990792913180520071883 / 2654864440966865408000 : ℝ) ≤ (2488943995978117441827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (500653 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_308 : rowCell 2 308 ≤ (191789317410931983191 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (277125771630092933101 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2488943995978117441827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_308_1
  · norm_num [gridPoint]

theorem exp_2_309_0 : expNegUpper (9478826748993464072187 / 106635516343910912000 : ℝ) ≤ (1244471895643822635947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (500653 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_309_1 : expNegUpper (4745150446544240895029 / 53317758171955456000 : ℝ) ≤ (558758765733980992477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_309 : rowCell 2 309 ≤ (344476782249734510601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1244471895643822635947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (558758765733980992477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_309_1
  · norm_num [gridPoint]

theorem exp_2_310_0 : expNegUpper (39706769472383640876767 / 446155702422405888000 : ℝ) ≤ (2235034880642292709417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004297 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_310_1 : expNegUpper (79509693816594640683467 / 892311404844811776000 : ℝ) ≤ (1003355950763155682809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (401197 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_310 : rowCell 2 310 ≤ (309311986300109213757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2235034880642292709417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1003355950763155682809 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_310_1
  · norm_num [gridPoint]

theorem exp_2_311_0 : expNegUpper (239515401313866539155289 / 2688003358776852992000 : ℝ) ≤ (100335586960087092239 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (401197 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_311_1 : expNegUpper (1199027401366173993489 / 13440016793884264960 : ℝ) ≤ (1801430888417151678299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_311 : rowCell 2 311 ≤ (277693181784111717053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (100335586960087092239 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1801430888417151678299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_311_1
  · norm_num [gridPoint]

theorem exp_2_312_0 : expNegUpper (1203975160779346651089 / 13495476706625128960 : ℝ) ≤ (18014307438943701143 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2007677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_312_1 : expNegUpper (241086728789903321422711 / 2699095341325025792000 : ℝ) ≤ (1616897526583080679917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_312 : rowCell 2 312 ≤ (249267568637521219 / 1000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18014307438943701143 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1616897526583080679917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_312_1
  · norm_num [gridPoint]

theorem exp_2_313_0 : expNegUpper (11527596159649945960819 / 129057626770426368000 : ℝ) ≤ (1616897397927674277943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_313_1 : expNegUpper (5770781833145908022719 / 64528813385213184000 : ℝ) ≤ (725521224309110605933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (31423 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_313 : rowCell 2 313 ≤ (44743385992466516039 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1616897397927674277943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (725521224309110605933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_313_1
  · norm_num [gridPoint]

theorem exp_2_314_0 : expNegUpper (4867377457930875815251 / 54426956426772736000 : ℝ) ≤ (725521167051945925317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (31423 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_314_1 : expNegUpper (9746552594889915680853 / 108853912853545472000 : ℝ) ≤ (1301999688514743730667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251597 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_314 : rowCell 2 314 ≤ (200754297725543103019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (725521167051945925317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1301999688514743730667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_314_1
  · norm_num [gridPoint]

theorem exp_2_315_0 : expNegUpper (244663102779892753702917 / 2732508318804075008000 : ℝ) ≤ (325499896650289993107 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (251597 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_315_1 : expNegUpper (61239918105650308338289 / 683127079701018752000 : ℝ) ≤ (584043506002569424281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2014483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_315 : rowCell 2 315 ≤ (90060466994399872687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (325499896650289993107 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (584043506002569424281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_315_1
  · norm_num [gridPoint]

theorem exp_2_316_0 : expNegUpper (20496851582919533393947 / 228640971214605696000 : ℝ) ≤ (584043460659058528913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2014483 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_316_1 : expNegUpper (16417361309035120511917 / 182912776971684556800 : ℝ) ≤ (523894057256395598931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1008097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_316 : rowCell 2 316 ≤ (161583598438017334337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (584043460659058528913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (523894057256395598931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_316_1
  · norm_num [gridPoint]

theorem exp_2_317_0 : expNegUpper (49453246306861475712991 / 550979565730443366400 : ℝ) ≤ (1047788033826564037129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1008097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_317_1 : expNegUpper (123783033251681630863593 / 1377448914326108416000 : ℝ) ≤ (234934128260325987251 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_317 : rowCell 2 317 ≤ (144932075624190010149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1047788033826564037129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (234934128260325987251 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_317_1
  · norm_num [gridPoint]

theorem exp_2_318_0 : expNegUpper (124287575195025166972377 / 1383063420517460224000 : ℝ) ≤ (93973644126265924421 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2017909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_318_1 : expNegUpper (248876623018449242227513 / 2766126841034920448000 : ℝ) ≤ (168540194819707905257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504907 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_318 : rowCell 2 318 ≤ (64988468868376988961 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93973644126265924421 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (168540194819707905257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_318_1
  · norm_num [gridPoint]

theorem exp_2_319_0 : expNegUpper (3331853140728025514611 / 37031715889645056000 : ℝ) ≤ (842700910252634731417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504907 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_319_1 : expNegUpper (52123353994400707481 / 578620560775704000 : ℝ) ≤ (755572334125656317687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021351 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_319 : rowCell 2 319 ≤ (58273760464341489711 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (842700910252634731417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (755572334125656317687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_319_1
  · norm_num [gridPoint]

theorem sum_2_288_2 : blockSum (rowCell 2) 288 2 ≤ (6048175732853615077929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_288) (by simpa only [blockSum_one] using cell_2_289) (by norm_num)

theorem sum_2_290_2 : blockSum (rowCell 2) 290 2 ≤ (4909347754085002692257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_290) (by simpa only [blockSum_one] using cell_2_291) (by norm_num)

theorem sum_2_288_4 : blockSum (rowCell 2) 288 4 ≤ (5478761743469308885093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_288_2 sum_2_290_2 (by norm_num)

theorem sum_2_292_2 : blockSum (rowCell 2) 292 2 ≤ (3982116540093889452701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_292) (by simpa only [blockSum_one] using cell_2_293) (by norm_num)

theorem sum_2_294_2 : blockSum (rowCell 2) 294 2 ≤ (1613871203037697119713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_294) (by simpa only [blockSum_one] using cell_2_295) (by norm_num)

theorem sum_2_292_4 : blockSum (rowCell 2) 292 4 ≤ (7209858946169283692127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_292_2 sum_2_294_2 (by norm_num)

theorem sum_2_288_8 : blockSum (rowCell 2) 288 8 ≤ (18167382433107901462313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_288_4 sum_2_292_4 (by norm_num)

theorem sum_2_296_2 : blockSum (rowCell 2) 296 2 ≤ (522892472489034982593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_296) (by simpa only [blockSum_one] using cell_2_297) (by norm_num)

theorem sum_2_298_2 : blockSum (rowCell 2) 298 2 ≤ (33066512728603545071 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_298) (by simpa only [blockSum_one] using cell_2_299) (by norm_num)

theorem sum_2_296_4 : blockSum (rowCell 2) 296 4 ≤ (4730719177075801797509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_296_2 sum_2_298_2 (by norm_num)

theorem sum_2_300_2 : blockSum (rowCell 2) 300 2 ≤ (2738927509050446599 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_300) (by simpa only [blockSum_one] using cell_2_301) (by norm_num)

theorem sum_2_302_2 : blockSum (rowCell 2) 302 2 ≤ (1383765979527351428187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_302) (by simpa only [blockSum_one] using cell_2_303) (by norm_num)

theorem sum_2_300_4 : blockSum (rowCell 2) 300 4 ≤ (1547797836341940276281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_300_2 sum_2_302_2 (by norm_num)

theorem sum_2_296_8 : blockSum (rowCell 2) 296 8 ≤ (7826314849759682350071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_296_4 sum_2_300_4 (by norm_num)

theorem sum_2_288_16 : blockSum (rowCell 2) 288 16 ≤ (812303040089611994137 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_288_8 sum_2_296_8 (by norm_num)

theorem sum_2_304_2 : blockSum (rowCell 2) 304 2 ≤ (1117836501725832589687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_304) (by simpa only [blockSum_one] using cell_2_305) (by norm_num)

theorem sum_2_306_2 : blockSum (rowCell 2) 306 2 ≤ (225606211667378736739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_306) (by simpa only [blockSum_one] using cell_2_307) (by norm_num)

theorem sum_2_304_4 : blockSum (rowCell 2) 304 4 ≤ (2020261348395347536643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_304_2 sum_2_306_2 (by norm_num)

theorem sum_2_308_2 : blockSum (rowCell 2) 308 2 ≤ (728055417071598476983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_308) (by simpa only [blockSum_one] using cell_2_309) (by norm_num)

theorem sum_2_310_2 : blockSum (rowCell 2) 310 2 ≤ (58700516808422093081 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_310) (by simpa only [blockSum_one] using cell_2_311) (by norm_num)

theorem sum_2_308_4 : blockSum (rowCell 2) 308 4 ≤ (1315060585155819407793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_308_2 sum_2_310_2 (by norm_num)

theorem sum_2_304_8 : blockSum (rowCell 2) 304 8 ≤ (833830483387791736109 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_304_4 sum_2_308_4 (by norm_num)

theorem sum_2_312_2 : blockSum (rowCell 2) 312 2 ≤ (94596899719970759839 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_312) (by simpa only [blockSum_one] using cell_2_313) (by norm_num)

theorem sum_2_314_2 : blockSum (rowCell 2) 314 2 ≤ (380875231714342848393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_314) (by simpa only [blockSum_one] using cell_2_315) (by norm_num)

theorem sum_2_312_4 : blockSum (rowCell 2) 312 4 ≤ (213464932578549161897 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_312_2 sum_2_314_2 (by norm_num)

theorem sum_2_316_2 : blockSum (rowCell 2) 316 2 ≤ (153257837031103672243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_316) (by simpa only [blockSum_one] using cell_2_317) (by norm_num)

theorem sum_2_318_2 : blockSum (rowCell 2) 318 2 ≤ (7703889333294904917 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_318) (by simpa only [blockSum_one] using cell_2_319) (by norm_num)

theorem sum_2_316_4 : blockSum (rowCell 2) 316 4 ≤ (55304013272764430183 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_316_2 sum_2_318_2 (by norm_num)

theorem sum_2_312_8 : blockSum (rowCell 2) 312 8 ≤ (703449931520920474709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_312_4 sum_2_316_4 (by norm_num)

theorem sum_2_304_16 : blockSum (rowCell 2) 304 16 ≤ (2371110898296503946927 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_304_8 sum_2_312_8 (by norm_num)

theorem sum_2_288_32 : blockSum (rowCell 2) 288 32 ≤ (15367959539730295853119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_288_16 sum_2_304_16 (by norm_num)

#print axioms sum_2_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
