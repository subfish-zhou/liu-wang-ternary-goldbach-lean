import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_288_0 : expNegUpper (6501005961221397731607 / 76224722892415504000 : ℝ) ≤ (91327370692154110417147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_288_1 : expNegUpper (208293264230616785792623 / 2439191132557296128000 : ℝ) ≤ (16411459037921359804343 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_288 : rowCell 1 288 ≤ (12643365611383758660849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91327370692154110417147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16411459037921359804343 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_288_1
  · norm_num [gridPoint]

theorem exp_1_289_0 : expNegUpper (2789274687898250374229 / 32663437787641344000 : ℝ) ≤ (3282291510697905398093 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_289_1 : expNegUpper (1396388107537579621253 / 16331718893820672000 : ℝ) ≤ (14743164014903307830481 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (243787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_289 : rowCell 1 289 ≤ (2271822995247520868081 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3282291510697905398093 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14743164014903307830481 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_289_1
  · norm_num [gridPoint]

theorem exp_1_290_0 : expNegUpper (105181819478320348925671 / 1230173686947330304000 : ℝ) ≤ (18428953366046520390447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (243787 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_290_1 : expNegUpper (210627797892424518621381 / 2460347373894660608000 : ℝ) ≤ (33105639345141064477967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487983 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_290 : rowCell 1 290 ≤ (5101804637825339720493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18428953366046520390447 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33105639345141064477967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_290_1
  · norm_num [gridPoint]

theorem exp_1_291_0 : expNegUpper (16272024064941471807153 / 190073827078613504000 : ℝ) ≤ (2648450912154115143367 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (487983 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_291_1 : expNegUpper (814623151955069841623 / 9503691353930675200 : ℝ) ≤ (29730450402182060735747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_291 : rowCell 1 291 ≤ (9164127808104659776521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2648450912154115143367 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29730450402182060735747 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_291_1
  · norm_num [gridPoint]

theorem exp_1_292_0 : expNegUpper (3545227220791712195353 / 41359916140917427200 : ℝ) ≤ (929076493177035067397 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_292_1 : expNegUpper (70993630323552170172937 / 827198322818348544000 : ℝ) ≤ (53389971615930897120719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1955217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_292 : rowCell 1 292 ≤ (8229186624162703800809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (929076493177035067397 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (53389971615930897120719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_292_1
  · norm_num [gridPoint]

theorem exp_1_293_0 : expNegUpper (213895610158770139264979 / 2492253023193870848000 : ℝ) ≤ (53389966950210461942257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1955217 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_293_1 : expNegUpper (107082211135889110220469 / 1246126511596935424000 : ℝ) ≤ (5991382722044473219353 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (391373 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_293 : rowCell 1 293 ≤ (1477684089070591461287 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (53389966950210461942257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5991382722044473219353 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_293_1
  · norm_num [gridPoint]

theorem exp_1_294_0 : expNegUpper (4301645071407600057069 / 50058678324769024000 : ℝ) ≤ (15337938439487137603 / 320000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (391373 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_294_1 : expNegUpper (8614104936160877412697 / 100117356649538048000 : ℝ) ≤ (21511664758816271553609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (979259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_294 : rowCell 1 294 ≤ (6632475627156093543667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15337938439487137603 / 320000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21511664758816271553609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_294_1
  · norm_num [gridPoint]

theorem exp_1_295_0 : expNegUpper (72091191158223656405219 / 837879215862928896000 : ℝ) ≤ (1344478931925470923143 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (979259 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_295_1 : expNegUpper (9022729348321929244889 / 104734901982866112000 : ℝ) ≤ (965297207329551188051 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_295 : rowCell 1 295 ≤ (5952913157388687039241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1344478931925470923143 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (965297207329551188051 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_295_1
  · norm_num [gridPoint]

theorem exp_1_296_0 : expNegUpper (27183697482997710635083 / 315545527155609664000 : ℝ) ≤ (38611885004299168493207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (980087 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_296_1 : expNegUpper (43548615026245993369947 / 504872843448975462400 : ℝ) ≤ (1082726060073394873811 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_296 : rowCell 1 296 ≤ (333882548179426160063 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38611885004299168493207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1082726060073394873811 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_296_1
  · norm_num [gridPoint]

theorem exp_1_297_0 : expNegUpper (43734056546130159435507 / 507022725041344614400 : ℝ) ≤ (6929446199233537751411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1961833 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_297_1 : expNegUpper (109472672855435788481843 / 1267556812603361536000 : ℝ) ≤ (31084725766202969930171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_297 : rowCell 1 297 ≤ (2396616671583486061931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6929446199233537751411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31084725766202969930171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_297_1
  · norm_num [gridPoint]

theorem exp_1_298_0 : expNegUpper (1182127376704392216319 / 13687558448786688000 : ℝ) ≤ (31084723163091684684593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1963497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_298_1 : expNegUpper (2367229312806341709121 / 27375116897573376000 : ℝ) ≤ (27884116952251591719229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393033 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_298 : rowCell 1 298 ≤ (1075015200257030711023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31084723163091684684593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27884116952251591719229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_298_1
  · norm_num [gridPoint]

theorem exp_1_299_0 : expNegUpper (353737308584670075173 / 4090689529676288000 : ℝ) ≤ (27884114636865163558407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (393033 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_299_1 : expNegUpper (88545610505569287813 / 1022672382419072000 : ℝ) ≤ (3126141139143320578067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491709 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_299 : rowCell 1 299 ≤ (3857022855524536870263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27884114636865163558407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3126141139143320578067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_299_1
  · norm_num [gridPoint]

theorem exp_1_300_0 : expNegUpper (55575167529548744537493 / 641874719731697792000 : ℝ) ≤ (25009127053968871943679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491709 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_300_1 : expNegUpper (222580456222010545445491 / 2567498878926791168000 : ℝ) ≤ (5606766878258501088537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_300 : rowCell 1 300 ≤ (691817985256381206257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25009127053968871943679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5606766878258501088537 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_300_1
  · norm_num [gridPoint]

theorem exp_1_301_0 : expNegUpper (74506752939228047488313 / 859446546703885824000 : ℝ) ≤ (22427065681967333609851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1968511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_301_1 : expNegUpper (7460054198586346780543 / 85944654670388582400 : ℝ) ≤ (20108472808039394735731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (197019 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_301 : rowCell 1 301 ≤ (155086484110707637319 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22427065681967333609851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20108472808039394735731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_301_1
  · norm_num [gridPoint]

theorem exp_1_302_0 : expNegUpper (22474459395622493665709 / 258920323960227891200 : ℝ) ≤ (5027117795009402698761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (197019 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_302_1 : expNegUpper (225027545463001440173961 / 2589203239602278912000 : ℝ) ≤ (18026806027561867294969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_302 : rowCell 1 302 ≤ (139042933807063507249 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5027117795009402698761 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18026806027561867294969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_302_1
  · norm_num [gridPoint]

theorem exp_1_303_0 : expNegUpper (225973685526156007455489 / 2600089677398655488000 : ℝ) ≤ (9013402290151244337997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1971873 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_303_1 : expNegUpper (14141139045661393902973 / 162505604837415968000 : ℝ) ≤ (16158163673300054194863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1973559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_303 : rowCell 1 303 ≤ (1246399299055056386089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9013402290151244337997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16158163673300054194863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_303_1
  · norm_num [gridPoint]

theorem exp_1_304_0 : expNegUpper (14564586123065128307 / 167371727788512000 : ℝ) ≤ (807908119344558010787 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1973559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_304_1 : expNegUpper (233326844874535012273 / 2677947644616192000 : ℝ) ≤ (7240510057898562900667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7901 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_304 : rowCell 1 304 ≤ (2234236715486559575373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (807908119344558010787 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7240510057898562900667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_304_1
  · norm_num [gridPoint]

theorem exp_1_305_0 : expNegUpper (228446177929543565787287 / 2621931067908674048000 : ℝ) ≤ (2896203794503088590161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (7901 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_305_1 : expNegUpper (114366951260804045229423 / 1310965533954337024000 : ℝ) ≤ (2595198945220989935199 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (123559 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_305 : rowCell 1 305 ≤ (1001095053657071942303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2896203794503088590161 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2595198945220989935199 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_305_1
  · norm_num [gridPoint]

theorem exp_1_306_0 : expNegUpper (114844799373838673389407 / 1316443010311158016000 : ℝ) ≤ (3243998427540460535263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (123559 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_306_1 : expNegUpper (45995784205946061930929 / 526577204124463206400 : ℝ) ≤ (2325128283013941687317 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_306 : rowCell 1 306 ≤ (1793973336363442493343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3243998427540460535263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2325128283013941687317 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_306_1
  · norm_num [gridPoint]

theorem exp_1_307_0 : expNegUpper (15395854397770399419523 / 176257587442780876800 : ℝ) ≤ (1453205064050267115613 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (989321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_307_1 : expNegUpper (19269061605781411773553 / 220321984303476096000 : ℝ) ≤ (2603564616675280755813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (247543 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_307 : rowCell 1 307 ≤ (321433847005589750701 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1453205064050267115613 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2603564616675280755813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_307_1
  · norm_num [gridPoint]

theorem exp_1_308_0 : expNegUpper (58047709894629536514611 / 663716110241716352000 : ℝ) ≤ (1041425766478494063889 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (247543 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_308_1 : expNegUpper (232483367232886632071883 / 2654864440966865408000 : ℝ) ≤ (4663858373455057866789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982049 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_308 : rowCell 1 308 ≤ (719801255515469508979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1041425766478494063889 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4663858373455057866789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_308_1
  · norm_num [gridPoint]

theorem exp_1_309_0 : expNegUpper (9337947183036098312187 / 106635516343910912000 : ℝ) ≤ (4663858017296671583409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1982049 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_309_1 : expNegUpper (4674856298251960575029 / 53317758171955456000 : ℝ) ≤ (2088326136560377825347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991879 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_309 : rowCell 1 309 ≤ (1289315906046405681637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4663858017296671583409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2088326136560377825347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_309_1
  · norm_num [gridPoint]

theorem exp_1_310_0 : expNegUpper (39118557658507928876767 / 446155702422405888000 : ℝ) ≤ (8353303913595479100993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (991879 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_310_1 : expNegUpper (78335697433616592683467 / 892311404844811776000 : ℝ) ≤ (1495917495321564857237 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_310 : rowCell 1 310 ≤ (577274332518491634387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8353303913595479100993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1495917495321564857237 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_310_1
  · norm_num [gridPoint]

theorem exp_1_311_0 : expNegUpper (235978848696292139155289 / 2688003358776852992000 : ℝ) ≤ (747958691479429031079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1985471 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_311_1 : expNegUpper (1181381046949902633489 / 13440016793884264960 : ℝ) ≤ (418517624302448619109 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (496797 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_311 : rowCell 1 311 ≤ (64607318536573163159 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (747958691479429031079 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (418517624302448619109 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_311_1
  · norm_num [gridPoint]

theorem exp_1_312_0 : expNegUpper (1186255989019874011089 / 13495476706625128960 : ℝ) ≤ (6696281489991725739019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (496797 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_312_1 : expNegUpper (237550176172328921422711 / 2699095341325025792000 : ℝ) ≤ (119882824227562000939 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (497227 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_312 : rowCell 1 312 ≤ (462698512467766729133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6696281489991725739019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119882824227562000939 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_312_1
  · norm_num [gridPoint]

theorem exp_1_313_0 : expNegUpper (79509467755478069725733 / 903403387392984576000 : ℝ) ≤ (2997070384248150748031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (497227 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_313_1 : expNegUpper (39804833773372268159033 / 451701693696492288000 : ℝ) ≤ (5364851931834103532999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_313 : rowCell 1 313 ≤ (414153976526548668909 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2997070384248150748031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5364851931834103532999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_313_1
  · norm_num [gridPoint]

theorem exp_1_314_0 : expNegUpper (4796209501520180135251 / 54426956426772736000 : ℝ) ≤ (2682425769344543686251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1990633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_314_1 : expNegUpper (9604507951441329440853 / 108853912853545472000 : ℝ) ≤ (2400470826720274416323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (49809 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_314 : rowCell 1 314 ≤ (14825975457998282521 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2682425769344543686251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2400470826720274416323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_314_1
  · norm_num [gridPoint]

theorem exp_1_315_0 : expNegUpper (241097423225037841702917 / 2732508318804075008000 : ℝ) ≤ (2400470652245380281157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (49809 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_315_1 : expNegUpper (60350318650516612338289 / 683127079701018752000 : ℝ) ≤ (214784737935172768477 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (498523 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_315 : rowCell 1 315 ≤ (132666974897417050361 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2400470652245380281157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (214784737935172768477 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_315_1
  · norm_num [gridPoint]

theorem exp_1_316_0 : expNegUpper (20199104808821613393947 / 228640971214605696000 : ℝ) ≤ (4295694449019520596053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (498523 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_316_1 : expNegUpper (16179649338711459711917 / 182912776971684556800 : ℝ) ≤ (384307690359336163643 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_316 : rowCell 1 316 ≤ (59348651920991848553 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4295694449019520596053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (384307690359336163643 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_316_1
  · norm_num [gridPoint]

theorem exp_1_317_0 : expNegUpper (3749015207858649393307 / 42383043517726412800 : ℝ) ≤ (3843076628791080269627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1995827 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_317_1 : expNegUpper (9384350200545700835661 / 105957608794316032000 : ℝ) ≤ (1718833424162534545083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (998783 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_317 : rowCell 1 317 ≤ (530918355644277332857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3843076628791080269627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1718833424162534545083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_317_1
  · norm_num [gridPoint]

theorem exp_1_318_0 : expNegUpper (122493812816117518972377 / 1383063420517460224000 : ℝ) ≤ (859416651126417554671 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (998783 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_318_1 : expNegUpper (245296379994954074227513 / 2766126841034920448000 : ℝ) ≤ (3074595005843801942037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_318 : rowCell 1 318 ≤ (237439983743362029157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (859416651126417554671 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3074595005843801942037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_318_1
  · norm_num [gridPoint]

theorem exp_1_319_0 : expNegUpper (3283922387499553194611 / 37031715889645056000 : ℝ) ≤ (768648697385170309677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1999309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_319_1 : expNegUpper (51375953003189187481 / 578620560775704000 : ℝ) ≤ (2749488057273059493519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (400211 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_319 : rowCell 1 319 ≤ (84939470752818131683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (768648697385170309677 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2749488057273059493519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_319_1
  · norm_num [gridPoint]

theorem sum_1_288_2 : blockSum (rowCell 1) 288 2 ≤ (12001240293810681500627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_288) (by simpa only [blockSum_one] using cell_1_289) (by norm_num)

theorem sum_1_290_2 : blockSum (rowCell 1) 290 2 ≤ (19367737083755339217507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_290) (by simpa only [blockSum_one] using cell_1_291) (by norm_num)

theorem sum_1_288_4 : blockSum (rowCell 1) 288 4 ≤ (43370217671376702218761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_288_2 sum_1_290_2 (by norm_num)

theorem sum_1_292_2 : blockSum (rowCell 1) 292 2 ≤ (3904401767378915276811 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_292) (by simpa only [blockSum_one] using cell_1_293) (by norm_num)

theorem sum_1_294_2 : blockSum (rowCell 1) 294 2 ≤ (3146347196136195145727 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_294) (by simpa only [blockSum_one] using cell_1_295) (by norm_num)

theorem sum_1_292_4 : blockSum (rowCell 1) 292 4 ≤ (3525374481757555211269 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_292_2 sum_1_294_2 (by norm_num)

theorem sum_1_288_8 : blockSum (rowCell 1) 288 8 ≤ (71573213525437143908913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_288_4 sum_1_292_4 (by norm_num)

theorem sum_1_296_2 : blockSum (rowCell 1) 296 2 ≤ (1013535411403779068487 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_296) (by simpa only [blockSum_one] using cell_1_297) (by norm_num)

theorem sum_1_298_2 : blockSum (rowCell 1) 298 2 ≤ (1631416731310531942871 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_298) (by simpa only [blockSum_one] using cell_1_299) (by norm_num)

theorem sum_1_296_4 : blockSum (rowCell 1) 296 4 ≤ (731697510823618015969 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_296_2 sum_1_298_2 (by norm_num)

theorem sum_1_300_2 : blockSum (rowCell 1) 300 2 ≤ (1312163921699211755533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_300) (by simpa only [blockSum_one] using cell_1_301) (by norm_num)

theorem sum_1_302_2 : blockSum (rowCell 1) 302 2 ≤ (2636828637125691458579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_302) (by simpa only [blockSum_one] using cell_1_303) (by norm_num)

theorem sum_1_300_4 : blockSum (rowCell 1) 300 4 ≤ (11834476882747441694823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_300_2 sum_1_302_2 (by norm_num)

theorem sum_1_296_8 : blockSum (rowCell 1) 296 8 ≤ (941466082916809127939 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_296_4 sum_1_300_4 (by norm_num)

theorem sum_1_288_16 : blockSum (rowCell 1) 288 16 ≤ (101700128178775036002961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_288_8 sum_1_296_8 (by norm_num)

theorem sum_1_304_2 : blockSum (rowCell 1) 304 2 ≤ (4236426822800703459979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_304) (by simpa only [blockSum_one] using cell_1_305) (by norm_num)

theorem sum_1_306_2 : blockSum (rowCell 1) 306 2 ≤ (6642856584748811029 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_306) (by simpa only [blockSum_one] using cell_1_307) (by norm_num)

theorem sum_1_304_4 : blockSum (rowCell 1) 304 4 ≤ (7637569394192094706827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_304_2 sum_1_306_2 (by norm_num)

theorem sum_1_308_2 : blockSum (rowCell 1) 308 2 ≤ (545783683415468939919 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_308) (by simpa only [blockSum_one] using cell_1_309) (by norm_num)

theorem sum_1_310_2 : blockSum (rowCell 1) 310 2 ≤ (1094132880811076939659 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_310) (by simpa only [blockSum_one] using cell_1_311) (by norm_num)

theorem sum_1_308_4 : blockSum (rowCell 1) 308 4 ≤ (4917184178699498578913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_308_2 sum_1_310_2 (by norm_num)

theorem sum_1_304_8 : blockSum (rowCell 1) 304 8 ≤ (627737678644579664287 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_304_4 sum_1_308_4 (by norm_num)

theorem sum_1_312_2 : blockSum (rowCell 1) 312 2 ≤ (438426244497157699021 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_312) (by simpa only [blockSum_one] using cell_1_313) (by norm_num)

theorem sum_1_314_2 : blockSum (rowCell 1) 314 2 ≤ (280926729477399875571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_314) (by simpa only [blockSum_one] using cell_1_315) (by norm_num)

theorem sum_1_312_4 : blockSum (rowCell 1) 312 4 ≤ (3158338625375630173939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_312_2 sum_1_314_2 (by norm_num)

theorem sum_1_316_2 : blockSum (rowCell 1) 316 2 ≤ (1124404874854195818387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_316) (by simpa only [blockSum_one] using cell_1_317) (by norm_num)

theorem sum_1_318_2 : blockSum (rowCell 1) 318 2 ≤ (899577321250814716729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_318) (by simpa only [blockSum_one] using cell_1_319) (by norm_num)

theorem sum_1_316_4 : blockSum (rowCell 1) 316 4 ≤ (505995549026252633779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_316_2 sum_1_318_2 (by norm_num)

theorem sum_1_312_8 : blockSum (rowCell 1) 312 8 ≤ (1036464164296128141811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_312_4 sum_1_316_4 (by norm_num)

theorem sum_1_304_16 : blockSum (rowCell 1) 304 16 ≤ (3547414878874446798959 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_304_8 sum_1_312_8 (by norm_num)

theorem sum_1_288_32 : blockSum (rowCell 1) 288 32 ≤ (29859300643286817499439 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_288_16 sum_1_304_16 (by norm_num)

#print axioms sum_1_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
