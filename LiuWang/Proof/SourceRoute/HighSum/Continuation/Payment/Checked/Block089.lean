import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_288_0 : expNegUpper (6781762021905685731607 / 76224722892415504000 : ℝ) ≤ (574008231654482751489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (16031 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_288_1 : expNegUpper (217258040214326993792623 / 2439191132557296128000 : ℝ) ≤ (2079465379806336208827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2005427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_288 : rowCell 5 288 ≤ (63813053523243448671 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (574008231654482751489 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2079465379806336208827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_288_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_288_1
  · norm_num [gridPoint]

theorem exp_5_289_0 : expNegUpper (8727968539698120082687 / 97990313362924032000 : ℝ) ≤ (1039732576567134035607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2005427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_289_1 : expNegUpper (4368848201450683183759 / 48995156681462016000 : ℝ) ≤ (7531779694355082071 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2006983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_289 : rowCell 5 289 ≤ (288942502772447279763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1039732576567134035607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7531779694355082071 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_289_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_289_1
  · norm_num [gridPoint]

theorem exp_5_290_0 : expNegUpper (109693334407455964925671 / 1230173686947330304000 : ℝ) ≤ (376588944020666675909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2006983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_290_1 : expNegUpper (219631409792508742621381 / 2460347373894660608000 : ℝ) ≤ (426163746604267393631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2008543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_290 : rowCell 5 290 ≤ (4087671778649673599 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (376588944020666675909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (426163746604267393631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_290_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_290_1
  · norm_num [gridPoint]

theorem exp_5_291_0 : expNegUpper (4693165120440369648787 / 52573611745148416000 : ℝ) ≤ (1704654803779679010533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2008543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_291_1 : expNegUpper (234920265283605734917 / 2628680587257420800 : ℝ) ≤ (771469725750219010741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502527 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_291 : rowCell 5 291 ≤ (47363498171097972441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1704654803779679010533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (771469725750219010741 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_291_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_291_1
  · norm_num [gridPoint]

theorem exp_5_292_0 : expNegUpper (11088774951107398986059 / 124079748422752281600 : ℝ) ≤ (77146964380235885447 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (502527 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_292_1 : expNegUpper (222023338787114750518811 / 2481594968455045632000 : ℝ) ≤ (279257817854188297987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_292 : rowCell 5 292 ≤ (26791396744345989751 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (77146964380235885447 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (279257817854188297987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_292_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_292_1
  · norm_num [gridPoint]

theorem exp_5_293_0 : expNegUpper (222976893891602395264979 / 2492253023193870848000 : ℝ) ≤ (698144471110033039953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011677 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_293_1 : expNegUpper (111613144023211734220469 / 1246126511596935424000 : ℝ) ≤ (631664443341499844881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8053 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_293 : rowCell 5 293 ≤ (193941721584004711023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (698144471110033039953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (631664443341499844881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_293_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_293_1
  · norm_num [gridPoint]

theorem exp_5_294_0 : expNegUpper (4483659105227985337069 / 50058678324769024000 : ℝ) ≤ (1263328754769205102583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8053 / 4000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_294_1 : expNegUpper (8977356285474167652697 / 100117356649538048000 : ℝ) ≤ (285701608514667890293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503707 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_294 : rowCell 5 294 ≤ (175457539731412478867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1263328754769205102583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (285701608514667890293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_294_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_294_1
  · norm_num [gridPoint]

theorem exp_5_295_0 : expNegUpper (225393693123877241215657 / 2513637647588786688000 : ℝ) ≤ (114280631574473000941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (503707 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_295_1 : expNegUpper (28205775756343195734667 / 314204705948598336000 : ℝ) ≤ (258395321172039200001 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2016409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_295 : rowCell 5 295 ≤ (31740827834360174013 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (114280631574473000941 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (258395321172039200001 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_295_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_295_1
  · norm_num [gridPoint]

theorem exp_5_296_0 : expNegUpper (28326139683921870635083 / 315545527155609664000 : ℝ) ≤ (1033581178590632305177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2016409 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_296_1 : expNegUpper (45372638956087247769947 / 504872843448975462400 : ℝ) ≤ (934615208855929084137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_296 : rowCell 5 296 ≤ (143522648874045103029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1033581178590632305177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (934615208855929084137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_296_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_296_1
  · norm_num [gridPoint]

theorem exp_5_297_0 : expNegUpper (45565847659246217035507 / 507022725041344614400 : ℝ) ≤ (934615113730046086469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (504499 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_297_1 : expNegUpper (114042441659132428481843 / 1267556812603361536000 : ℝ) ≤ (844963269964016300949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_297 : rowCell 5 297 ≤ (5190738183157005177 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (934615113730046086469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (844963269964016300949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_297_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_297_1
  · norm_num [gridPoint]

theorem exp_5_298_0 : expNegUpper (3694420412754584648957 / 41062675346360064000 : ℝ) ≤ (844963184689989303049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1009793 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_298_1 : expNegUpper (7397138117953873127363 / 82125350692720128000 : ℝ) ≤ (30550626239791155531 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_298 : rowCell 5 298 ≤ (117309952405051099233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (844963184689989303049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30550626239791155531 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_298_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_298_1
  · norm_num [gridPoint]

theorem exp_5_299_0 : expNegUpper (368453774955796961573 / 4090689529676288000 : ℝ) ≤ (152753115913093010249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2021181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_299_1 : expNegUpper (92216959915076206213 / 1022672382419072000 : ℝ) ≤ (172560051181031913053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101139 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_299 : rowCell 5 299 ≤ (53013704061859461309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (152753115913093010249 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172560051181031913053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_299_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_299_1
  · norm_num [gridPoint]

theorem exp_5_300_0 : expNegUpper (57879469889584072537493 / 641874719731697792000 : ℝ) ≤ (172560034058469248259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (101139 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_300_1 : expNegUpper (231778247703964849445491 / 2567498878926791168000 : ℝ) ≤ (623675565888934632351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_300 : rowCell 5 300 ≤ (95811913469934049687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172560034058469248259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (623675565888934632351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_300_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_300_1
  · norm_num [gridPoint]

theorem exp_5_301_0 : expNegUpper (232756886216012462464939 / 2578339640111657472000 : ℝ) ≤ (311837752261762031007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_301_1 : expNegUpper (23301883539773171541629 / 257833964011165747200 : ℝ) ≤ (563424947954399730617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202599 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_301 : rowCell 5 301 ≤ (43282215765126488047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (311837752261762031007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (563424947954399730617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_301_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_301_1
  · norm_num [gridPoint]

theorem exp_5_302_0 : expNegUpper (23400063931274026465709 / 258920323960227891200 : ℝ) ≤ (281712446490973860791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202599 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_302_1 : expNegUpper (234264172861329760173961 / 2589203239602278912000 : ℝ) ≤ (508900401241883706799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1013801 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_302 : rowCell 5 302 ≤ (39097461936029158491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (281712446490973860791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (508900401241883706799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_302_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_302_1
  · norm_num [gridPoint]

theorem exp_5_303_0 : expNegUpper (235249148840858343455489 / 2600089677398655488000 : ℝ) ≤ (508900352004651976751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1013801 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_303_1 : expNegUpper (14719641880443601902973 / 162505604837415968000 : ℝ) ≤ (229783796493686553959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1014609 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_303 : rowCell 5 303 ≤ (70621552656737797947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (508900352004651976751 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (229783796493686553959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_303_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_303_1
  · norm_num [gridPoint]

theorem exp_5_304_0 : expNegUpper (591256061981763363973 / 6527497383751968000 : ℝ) ≤ (459567548894370436801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1014609 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_304_1 : expNegUpper (9470765482694958918647 / 104439958140031488000 : ℝ) ≤ (103735258356539818097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015419 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_304 : rowCell 5 304 ≤ (12753990302823490999 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (459567548894370436801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (103735258356539818097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_304_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_304_1
  · norm_num [gridPoint]

theorem exp_5_305_0 : expNegUpper (237760477160619917787287 / 2621931067908674048000 : ℝ) ≤ (82988198789294101551 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1015419 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_305_1 : expNegUpper (119014391897248717229423 / 1310965533954337024000 : ℝ) ≤ (374579715260091732527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016231 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_305 : rowCell 5 305 ≤ (57572559450354696333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (82988198789294101551 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (374579715260091732527 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_305_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_305_1
  · norm_num [gridPoint]

theorem exp_5_306_0 : expNegUpper (119511657968470353389407 / 1316443010311158016000 : ℝ) ≤ (93644919979215563383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016231 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_306_1 : expNegUpper (47858644052161332330929 / 526577204124463206400 : ℝ) ≤ (33808313187831017009 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2034091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_306 : rowCell 5 306 ≤ (12992003129774736339 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93644919979215563383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33808313187831017009 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_306_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_306_1
  · norm_num [gridPoint]

theorem exp_5_307_0 : expNegUpper (48058190222801271858569 / 528772762328342630400 : ℝ) ≤ (169041550121661318469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2034091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_307_1 : expNegUpper (60140614114660075320659 / 660965952910428288000 : ℝ) ≤ (152543821243967132151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_307 : rowCell 5 307 ≤ (46900588408677425853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (169041550121661318469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (152543821243967132151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_307_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_307_1
  · norm_num [gridPoint]

theorem exp_5_308_0 : expNegUpper (60390848171038880514611 / 663716110241716352000 : ℝ) ≤ (38135951772090054469 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2035723 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_308_1 : expNegUpper (241836502380337000071883 / 2654864440966865408000 : ℝ) ≤ (68815788720995284907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (25467 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_308 : rowCell 5 308 ≤ (42319699488800436851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38135951772090054469 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68815788720995284907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_308_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_308_1
  · norm_num [gridPoint]

theorem exp_5_309_0 : expNegUpper (9713626025589073672187 / 106635516343910912000 : ℝ) ≤ (275263129551416949729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (25467 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_309_1 : expNegUpper (4862307360364708095029 / 53317758171955456000 : ℝ) ≤ (124155049481471368999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2039001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_309 : rowCell 5 309 ≤ (190897151105448009 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (275263129551416949729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124155049481471368999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_309_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_309_1
  · norm_num [gridPoint]

theorem exp_5_310_0 : expNegUpper (122061367486529482630301 / 1338467107267217664000 : ℝ) ≤ (49662015259855946653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2039001 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_310_1 : expNegUpper (244399063364674162050401 / 2676934214534435328000 : ℝ) ≤ (44791333255234846359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_310 : rowCell 5 310 ≤ (34438115170753635767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49662015259855946653 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44791333255234846359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_310_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_310_1
  · norm_num [gridPoint]

theorem exp_5_311_0 : expNegUpper (245409655676490539155289 / 2688003358776852992000 : ℝ) ≤ (223956646003464926187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020323 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_311_1 : expNegUpper (1228437992059959593489 / 13440016793884264960 : ℝ) ≤ (201956292940782350881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408459 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_311 : rowCell 5 311 ≤ (15528977081985297083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (223956646003464926187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (201956292940782350881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_311_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_311_1
  · norm_num [gridPoint]

theorem exp_5_312_0 : expNegUpper (1233507113711801051089 / 13495476706625128960 : ℝ) ≤ (201956274809661098923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (408459 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_312_1 : expNegUpper (246980983152527321422711 / 2699095341325025792000 : ℝ) ≤ (9104268254472559083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510987 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_312 : rowCell 5 312 ≤ (28004661418854114359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201956274809661098923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9104268254472559083 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_312_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_312_1
  · norm_num [gridPoint]

theorem exp_5_313_0 : expNegUpper (247998046163006625177199 / 2710210162178953728000 : ℝ) ≤ (91042674438117918547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (510987 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_313_1 : expNegUpper (124139613789309508477099 / 1355105081089476864000 : ℝ) ≤ (164141127758172273371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1022803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_313 : rowCell 5 313 ≤ (12623572869515570321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91042674438117918547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (164141127758172273371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_313_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_313_1
  · norm_num [gridPoint]

theorem exp_5_314_0 : expNegUpper (4985990718615368615251 / 54426956426772736000 : ℝ) ≤ (164141113262255225777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1022803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_314_1 : expNegUpper (9983293667304226080853 / 108853912853545472000 : ℝ) ≤ (147939779692949830501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2047267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_314 : rowCell 5 314 ≤ (11378609549735408573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (164141113262255225777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (147939779692949830501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_314_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_314_1
  · norm_num [gridPoint]

theorem exp_5_315_0 : expNegUpper (250605902037984273702917 / 2732508318804075008000 : ℝ) ≤ (147939766734450026441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2047267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_315_1 : expNegUpper (62722583864206468338289 / 683127079701018752000 : ℝ) ≤ (133314738013293716543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2048933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_315 : rowCell 5 315 ≤ (64091659924373697 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (147939766734450026441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133314738013293716543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_315_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_315_1
  · norm_num [gridPoint]

theorem exp_5_316_0 : expNegUpper (62979288619248200181841 / 685922913643817088000 : ℝ) ≤ (33328681607736000807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2048933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_316_1 : expNegUpper (50440643778723665535751 / 548738330915053670400 : ℝ) ≤ (120115058011068523223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1025301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_316 : rowCell 5 316 ≤ (369606551446670261 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33328681607736000807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (120115058011068523223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_316_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_316_1
  · norm_num [gridPoint]

theorem exp_5_317_0 : expNegUpper (50646660648026531712991 / 550979565730443366400 : ℝ) ≤ (120115047660315127299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1025301 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_317_1 : expNegUpper (126760500992660830863593 / 1377448914326108416000 : ℝ) ≤ (27050998649191250757 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513069 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_317 : rowCell 5 317 ≤ (16649229691775810949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120115047660315127299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27050998649191250757 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_317_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_317_1
  · norm_num [gridPoint]

theorem exp_5_318_0 : expNegUpper (127277179159871246972377 / 1383063420517460224000 : ℝ) ≤ (108203985348058198281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513069 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_318_1 : expNegUpper (254843694724274522227513 / 2766126841034920448000 : ℝ) ≤ (974576930396222519 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026977 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_318 : rowCell 5 318 ≤ (14997034362193834859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (108203985348058198281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (974576930396222519 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_318_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_318_1
  · norm_num [gridPoint]

theorem exp_5_319_0 : expNegUpper (10235213188326438143833 / 111095147668935168000 : ℝ) ≤ (1949153695537585981 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1026977 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_319_1 : expNegUpper (160107066939259722443 / 1735861682327112000 : ℝ) ≤ (87763997690806693947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (513909 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_319 : rowCell 5 319 ≤ (13506531495649004671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1949153695537585981 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87763997690806693947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_319_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_319_1
  · norm_num [gridPoint]

theorem sum_5_288_2 : blockSum (rowCell 5) 288 2 ≤ (304003885194332261559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_288) (by simpa only [blockSum_one] using cell_5_289) (by norm_num)

theorem sum_5_290_2 : blockSum (rowCell 5) 290 2 ≤ (498428484689068972541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_290) (by simpa only [blockSum_one] using cell_5_291) (by norm_num)

theorem sum_5_288_4 : blockSum (rowCell 5) 288 4 ≤ (1106436255077733495659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_288_2 sum_5_290_2 (by norm_num)

theorem sum_5_292_2 : blockSum (rowCell 5) 292 2 ≤ (408272895538772629031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_292) (by simpa only [blockSum_one] using cell_5_293) (by norm_num)

theorem sum_5_294_2 : blockSum (rowCell 5) 294 2 ≤ (83540419725803337233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_294) (by simpa only [blockSum_one] using cell_5_295) (by norm_num)

theorem sum_5_292_4 : blockSum (rowCell 5) 292 4 ≤ (742434574441985977963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_292_2 sum_5_294_2 (by norm_num)

theorem sum_5_288_8 : blockSum (rowCell 5) 288 8 ≤ (924435414759859736811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_288_4 sum_5_292_4 (by norm_num)

theorem sum_5_296_2 : blockSum (rowCell 5) 296 2 ≤ (136645551726485116227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_296) (by simpa only [blockSum_one] using cell_5_297) (by norm_num)

theorem sum_5_298_2 : blockSum (rowCell 5) 298 2 ≤ (223337360528770021851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_298) (by simpa only [blockSum_one] using cell_5_299) (by norm_num)

theorem sum_5_296_4 : blockSum (rowCell 5) 296 4 ≤ (99325692796348050861 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_296_2 sum_5_298_2 (by norm_num)

theorem sum_5_300_2 : blockSum (rowCell 5) 300 2 ≤ (182376345000187025781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_300) (by simpa only [blockSum_one] using cell_5_301) (by norm_num)

theorem sum_5_302_2 : blockSum (rowCell 5) 302 2 ≤ (148816476528796114929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_302) (by simpa only [blockSum_one] using cell_5_303) (by norm_num)

theorem sum_5_300_4 : blockSum (rowCell 5) 300 4 ≤ (33119282152898314071 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_300_2 sum_5_302_2 (by norm_num)

theorem sum_5_296_8 : blockSum (rowCell 5) 296 8 ≤ (165564257102144679003 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_296_4 sum_5_300_4 (by norm_num)

theorem sum_5_288_16 : blockSum (rowCell 5) 288 16 ≤ (2676692115030442868637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_288_8 sum_5_296_8 (by norm_num)

theorem sum_5_304_2 : blockSum (rowCell 5) 304 2 ≤ (3791953467639754729 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_304) (by simpa only [blockSum_one] using cell_5_305) (by norm_num)

theorem sum_5_306_2 : blockSum (rowCell 5) 306 2 ≤ (98868600927776371209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_306) (by simpa only [blockSum_one] using cell_5_307) (by norm_num)

theorem sum_5_304_4 : blockSum (rowCell 5) 304 4 ≤ (220211111892248522537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_304_2 sum_5_306_2 (by norm_num)

theorem sum_5_308_2 : blockSum (rowCell 5) 308 2 ≤ (80499129709890038651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_308) (by simpa only [blockSum_one] using cell_5_309) (by norm_num)

theorem sum_5_310_2 : blockSum (rowCell 5) 310 2 ≤ (65496069334724229933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_310) (by simpa only [blockSum_one] using cell_5_311) (by norm_num)

theorem sum_5_308_4 : blockSum (rowCell 5) 308 4 ≤ (18249399880576783573 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_308_2 sum_5_310_2 (by norm_num)

theorem sum_5_304_8 : blockSum (rowCell 5) 304 8 ≤ (366206310936862791121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_304_4 sum_5_308_4 (by norm_num)

theorem sum_5_312_2 : blockSum (rowCell 5) 312 2 ≤ (53251807157885255001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_312) (by simpa only [blockSum_one] using cell_5_313) (by norm_num)

theorem sum_5_314_2 : blockSum (rowCell 5) 314 2 ≤ (21633275137635200093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_314) (by simpa only [blockSum_one] using cell_5_315) (by norm_num)

theorem sum_5_312_4 : blockSum (rowCell 5) 312 4 ≤ (96518357433155655187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_312_2 sum_5_314_2 (by norm_num)

theorem sum_5_316_2 : blockSum (rowCell 5) 316 2 ≤ (35129557264109323999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_316) (by simpa only [blockSum_one] using cell_5_317) (by norm_num)

theorem sum_5_318_2 : blockSum (rowCell 5) 318 2 ≤ (2850356585784283953 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_318) (by simpa only [blockSum_one] using cell_5_319) (by norm_num)

theorem sum_5_316_4 : blockSum (rowCell 5) 316 4 ≤ (63633123121952163529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_316_2 sum_5_318_2 (by norm_num)

theorem sum_5_312_8 : blockSum (rowCell 5) 312 8 ≤ (40037870138776954679 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_312_4 sum_5_316_4 (by norm_num)

theorem sum_5_304_16 : blockSum (rowCell 5) 304 16 ≤ (526357791491970609837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_304_8 sum_5_312_8 (by norm_num)

theorem sum_5_288_32 : blockSum (rowCell 5) 288 32 ≤ (1601524953261206739237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_288_16 sum_5_304_16 (by norm_num)

#print axioms sum_5_288_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
