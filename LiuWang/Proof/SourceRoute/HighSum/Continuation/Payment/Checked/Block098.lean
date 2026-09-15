import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_64_0 : expNegUpper (31232200828479280943 / 404859561279048000 : ℝ) ≤ (78607950591079259062072379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456753 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_64_1 : expNegUpper (1998027996490793054503 / 25911011921859072000 : ℝ) ≤ (324702755252635807302945793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_64 : rowCell 6 64 ≤ (46606266163882310332826457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78607950591079259062072379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (324702755252635807302945793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_64_1
  · norm_num [gridPoint]

theorem exp_6_65_0 : expNegUpper (50371027732039483812167 / 653226219073131008000 : ℝ) ≤ (324702250116170476020980559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1826553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_65_1 : expNegUpper (25175500645429805817703 / 326613109536565504000 : ℝ) ≤ (334811052848239029228124253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456529 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_65 : rowCell 6 65 ≤ (12023075645911968302357399 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (324702250116170476020980559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (334811052848239029228124253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_65_1
  · norm_num [gridPoint]

theorem exp_6_66_0 : expNegUpper (25386461192821559966807 / 329349989202770176000 : ℝ) ≤ (6696210812500121525339237 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (456529 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_66_1 : expNegUpper (10150738849471989527201 / 131739995681108070400 : ℝ) ≤ (43091007002420185978618247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825699 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_66 : rowCell 6 66 ≤ (49552564990265205447856967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6696210812500121525339237 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43091007002420185978618247 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_66_1
  · norm_num [gridPoint]

theorem exp_6_67_0 : expNegUpper (10235443055743280920441 / 132839315208740966400 : ℝ) ≤ (86181884333766822568727999 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1825699 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_67_1 : expNegUpper (12789697193527370273359 / 166049144010926208000 : ℝ) ≤ (354425052091960503952925023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228163 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_67 : rowCell 6 67 ≤ (6372854370740428762547219 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86181884333766822568727999 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (354425052091960503952925023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_67_1
  · norm_num [gridPoint]

theorem exp_6_68_0 : expNegUpper (678735742152605059829 / 8812052789310848000 : ℝ) ≤ (354424527589111669705764401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (228163 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_68_1 : expNegUpper (2714015519128782038777 / 35248211157243392000 : ℝ) ≤ (9096847544735477603865209 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57029 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_68 : rowCell 6 68 ≤ (26189483408263804401820261 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (354424527589111669705764401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9096847544735477603865209 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_68_1
  · norm_num [gridPoint]

theorem exp_6_69_0 : expNegUpper (2079721430105060259883 / 27010331449491968000 : ℝ) ≤ (72774674424935814749309281 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (57029 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_69_1 : expNegUpper (1039524450154214545901 / 13505165724745984000 : ℝ) ≤ (186523592282484707998012851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912287 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_69 : rowCell 6 69 ≤ (26868454535435909364046681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (72774674424935814749309281 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (186523592282484707998012851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_69_1
  · norm_num [gridPoint]

theorem exp_6_70_0 : expNegUpper (26202291659070308590741 / 340411699396364544000 : ℝ) ≤ (186523325203239423623918039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (912287 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_70_1 : expNegUpper (52388581699239733497361 / 680823398792729088000 : ℝ) ≤ (381918338697043998303522633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_70 : rowCell 6 70 ≤ (13763181323571570898477907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (186523325203239423623918039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (381918338697043998303522633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_70_1
  · norm_num [gridPoint]

theorem exp_6_71_0 : expNegUpper (52818569092478963329289 / 686411349653914112000 : ℝ) ≤ (381917800721723114853915027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1824239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_71_1 : expNegUpper (1320084560759313101819 / 17160283741347852800 : ℝ) ≤ (97615448784868273021981357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_71 : rowCell 6 71 ≤ (56322614064991583953666181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (381917800721723114853915027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (97615448784868273021981357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_71_1
  · norm_num [gridPoint]

theorem exp_6_72_0 : expNegUpper (1330875076699504791739 / 17300553470521356800 : ℝ) ≤ (195230627015161904641141789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823923 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_72_1 : expNegUpper (53220634693447745750311 / 692022138820854272000 : ℝ) ≤ (6228954753003662250646657 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_72 : rowCell 6 72 ≤ (14385731992880039759197201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (195230627015161904641141789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6228954753003662250646657 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_72_1
  · norm_num [gridPoint]

theorem exp_6_73_0 : expNegUpper (53653895236982948931359 / 697655766293549568000 : ℝ) ≤ (199326280317829754868785457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_73_1 : expNegUpper (26820174240402022629539 / 348827883146774784000 : ℝ) ≤ (203234527069920017342734589 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823351 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_73 : rowCell 6 73 ≤ (58710191500880201642200027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (199326280317829754868785457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (203234527069920017342734589 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_73_1
  · norm_num [gridPoint]

theorem exp_6_74_0 : expNegUpper (1730408178938428219 / 22505991426304000 : ℝ) ≤ (25404281801437261855101067 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823351 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_74_1 : expNegUpper (3460002162225924437 / 45011982852608000 : ℝ) ≤ (51735972636531309968949563 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_74 : rowCell 6 74 ≤ (59821117699474007864499503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25404281801437261855101067 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51735972636531309968949563 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_74_1
  · norm_num [gridPoint]

theorem exp_6_75_0 : expNegUpper (54499094124847637135797 / 708991536156205568000 : ℝ) ≤ (413887234700450605250923673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1823093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_75_1 : expNegUpper (13621800149428616171629 / 177247884039051392000 : ℝ) ≤ (6576388583691201408416603 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_75 : rowCell 6 75 ≤ (6087262350196964059398027 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (413887234700450605250923673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6576388583691201408416603 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_75_1
  · norm_num [gridPoint]

theorem exp_6_76_0 : expNegUpper (13731355207096715384141 / 178673419636541568000 : ℝ) ≤ (420888322570417321244023017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_76_1 : expNegUpper (10982871782389175612663 / 142938735709233254400 : ℝ) ≤ (213726720881078651420296753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_76 : rowCell 6 76 ≤ (61861843637185234135764063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (420888322570417321244023017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (213726720881078651420296753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_76_1
  · norm_num [gridPoint]

theorem exp_6_77_0 : expNegUpper (11070849138956440355023 / 144083731848376422400 : ℝ) ≤ (5343161190705292517806879 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911317 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_77_1 : expNegUpper (27672009359906478093793 / 360209329620941056000 : ℝ) ≤ (13548882483467125263253749 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56951 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_77 : rowCell 6 77 ≤ (31393071517200952414458037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5343161190705292517806879 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13548882483467125263253749 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_77_1
  · norm_num [gridPoint]

theorem exp_6_78_0 : expNegUpper (27892789358186152290257 / 363083239121676544000 : ℝ) ≤ (433563693910211280149304657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56951 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_78_1 : expNegUpper (55776190013654345788393 / 726166478243353088000 : ℝ) ≤ (439205690887560612545447771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227781 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_78 : rowCell 6 78 ≤ (6364312766819768066348619 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (433563693910211280149304657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (439205690887560612545447771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_78_1
  · norm_num [gridPoint]

theorem exp_6_79_0 : expNegUpper (2248777195419832667273 / 29277485422023168000 : ℝ) ≤ (439205146925279095806796821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227781 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_79_1 : expNegUpper (140527206964521733987 / 1829842838876448000 : ℝ) ≤ (88872793881785327710460369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_79 : rowCell 6 79 ≤ (32215326897359119331214969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (439205146925279095806796821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (88872793881785327710460369 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_79_1
  · norm_num [gridPoint]

theorem exp_6_80_0 : expNegUpper (3540988074655711550507 / 46108164447722528000 : ℝ) ≤ (222181713842479581084239667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (911041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_80_1 : expNegUpper (56648107028614646335871 / 737730631163560448000 : ℝ) ≤ (112256759958920409944057877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_80 : rowCell 6 80 ≤ (16286708886775822588382203 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (222181713842479581084239667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (112256759958920409944057877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_80_1
  · norm_num [gridPoint]

theorem exp_6_81_0 : expNegUpper (1841765375345085667369 / 23985385970396672000 : ℝ) ≤ (449026500974265315683182911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821933 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_81_1 : expNegUpper (184154428175518873357 / 2398538597039667200 : ℝ) ≤ (45318469337626393684204553 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910901 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_81 : rowCell 6 81 ≤ (32895025436205258698882487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (449026500974265315683182911 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45318469337626393684204553 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_81_1
  · norm_num [gridPoint]

theorem exp_6_82_0 : expNegUpper (5753619220145327605187 / 74938613730678835200 : ℝ) ≤ (113296039496030749450726909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910901 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_82_1 : expNegUpper (57530189895535953538261 / 749386137306788352000 : ℝ) ≤ (3654628570148985328490819 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227711 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_82 : rowCell 6 82 ≤ (66358945806671688283113437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113296039496030749450726909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3654628570148985328490819 / 8000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_82_1
  · norm_num [gridPoint]

theorem exp_6_83_0 : expNegUpper (57980215884096892627469 / 755248147837035008000 : ℝ) ≤ (228414019966607994987354641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227711 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_83_1 : expNegUpper (14493767126082150364427 / 188812036959258752000 : ℝ) ≤ (45995217713771367765708881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_83 : rowCell 6 83 ≤ (3342621854926923301354199 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (228414019966607994987354641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45995217713771367765708881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_83_1
  · norm_num [gridPoint]

theorem exp_6_84_0 : expNegUpper (584268076759671521443 / 7611329966730368000 : ℝ) ≤ (1839806601702494289051423 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_84_1 : expNegUpper (2336900742125097649123 / 30445319866921472000 : ℝ) ≤ (46255087829537710976971301 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_84 : rowCell 6 84 ≤ (33634856602600508753932589 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1839806601702494289051423 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46255087829537710976971301 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_84_1
  · norm_num [gridPoint]

theorem exp_6_85_0 : expNegUpper (58875977569402701331427 / 767040683814793728000 : ℝ) ≤ (2312751783754255882592313 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_85_1 : expNegUpper (29436275017135559789213 / 383520341907396864000 : ℝ) ≤ (232310948136199878890232721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_85 : rowCell 6 85 ≤ (33805116848388266853044559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2312751783754255882592313 / 5000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (232310948136199878890232721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_85_1
  · norm_num [gridPoint]

theorem exp_6_86_0 : expNegUpper (29663867778371093458957 / 386485604631152896000 : ℝ) ≤ (46462138041603892260642171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821447 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_86_1 : expNegUpper (2373006917603931329513 / 30918848370492231680 : ℝ) ≤ (466164286949823598966932173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9107 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_86 : rowCell 6 86 ≤ (4242107944816669943139887 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46462138041603892260642171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (466164286949823598966932173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_86_1
  · norm_num [gridPoint]

theorem exp_6_87_0 : expNegUpper (125857035011208959227 / 1639841206348574720 : ℝ) ≤ (93232755455485140204962309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9107 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_87_1 : expNegUpper (393292087256234071943 / 5124503769839296000 : ℝ) ≤ (467178910727455145445049119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_87 : rowCell 6 87 ≤ (3403009367969358285485887 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93232755455485140204962309 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (467178910727455145445049119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_87_1
  · norm_num [gridPoint]

theorem exp_6_88_0 : expNegUpper (7529881972810944275653 / 98112596884324416000 : ℝ) ≤ (93435681541802364378173711 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821369 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_88_1 : expNegUpper (60238232995157653400023 / 784900775074595328000 : ℝ) ≤ (467668393231515243695100679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_88 : rowCell 6 88 ≤ (17042467156501488406828591 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93435681541802364378173711 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (467668393231515243695100679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_88_1
  · norm_num [gridPoint]

theorem exp_6_89_0 : expNegUpper (2427945520222829174567 / 31635992617574912000 : ℝ) ≤ (233833948655181123818580017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910677 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_89_1 : expNegUpper (1213973802581343067219 / 15817996308787456000 : ℝ) ≤ (467637077120168279946602717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364271 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_89 : rowCell 6 89 ≤ (8525409881067156375147357 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (233833948655181123818580017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (467637077120168279946602717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_89_1
  · norm_num [gridPoint]

theorem exp_6_90_0 : expNegUpper (30580424145956213919371 / 398460847054952704000 : ℝ) ≤ (467636588712287827034383947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (364271 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_90_1 : expNegUpper (61161778657014725547181 / 796921694109905408000 : ℝ) ≤ (467090965595023346499082107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_90 : rowCell 6 90 ≤ (68161173054376203748942817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (467636588712287827034383947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (467090965595023346499082107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_90_1
  · norm_num [gridPoint]

theorem exp_6_91_0 : expNegUpper (61625696633851296357989 / 802966411086193152000 : ℝ) ≤ (467090485088496109454280943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455343 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_91_1 : expNegUpper (3081375428566950834389 / 40148320554309657600 : ℝ) ≤ (466037658268471864873847857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455351 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_91 : rowCell 6 91 ≤ (17011135642726600490980397 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (467090485088496109454280943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (466037658268471864873847857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_91_1
  · norm_num [gridPoint]

theorem exp_6_92_0 : expNegUpper (3104659651186299082549 / 40451698318411801600 : ℝ) ≤ (93207437204615065946089091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455351 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_92_1 : expNegUpper (62095889864378673511811 / 809033966368236032000 : ℝ) ≤ (464486280070867775903147457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_92 : rowCell 6 92 ≤ (67854607164746900039810563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93207437204615065946089091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (464486280070867775903147457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_92_1
  · norm_num [gridPoint]

theorem exp_6_93_0 : expNegUpper (62563347453875130446779 / 815124359956034048000 : ℝ) ≤ (232242908208908421445205283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_93_1 : expNegUpper (31283466264236171374169 / 407562179978017024000 : ℝ) ≤ (231223701954053639116768411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_93 : rowCell 6 93 ≤ (1056137550277055054450169 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (232242908208908421445205283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (231223701954053639116768411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_93_1
  · norm_num [gridPoint]

theorem exp_6_94_0 : expNegUpper (1260723398332747789489 / 16424751836991744000 : ℝ) ≤ (231223474574966118579535359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (910757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_94_1 : expNegUpper (2521625862238346845057 / 32849503673983488000 : ℝ) ≤ (459932967799246734585674843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_94 : rowCell 6 94 ≤ (33630386122320382323804637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (231223474574966118579535359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (459932967799246734585674843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_94_1
  · norm_num [gridPoint]

theorem exp_6_95_0 : expNegUpper (63511670404351405463057 / 827373662048895488000 : ℝ) ≤ (459932522209803071318875203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1821591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_95_1 : expNegUpper (1984907560599259542973 / 25855426939027984000 : ℝ) ≤ (456956187235606672768583783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455421 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_95 : rowCell 6 95 ≤ (66860348459959170899174463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (459932522209803071318875203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (456956187235606672768583783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_95_1
  · norm_num [gridPoint]

theorem sum_6_64_2 : blockSum (rowCell 6) 64 2 ≤ (94698568747530183542256053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_64) (by simpa only [blockSum_one] using cell_6_65) (by norm_num)

theorem sum_6_66_2 : blockSum (rowCell 6) 66 2 ≤ (100535399956188635548234719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_66) (by simpa only [blockSum_one] using cell_6_67) (by norm_num)

theorem sum_6_64_4 : blockSum (rowCell 6) 64 4 ≤ (48808492175929704772622693 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_64_2 sum_6_66_2 (by norm_num)

theorem sum_6_68_2 : blockSum (rowCell 6) 68 2 ≤ (26528968971849856882933471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_68) (by simpa only [blockSum_one] using cell_6_69) (by norm_num)

theorem sum_6_70_2 : blockSum (rowCell 6) 70 2 ≤ (111375339359277867547577809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_70) (by simpa only [blockSum_one] using cell_6_71) (by norm_num)

theorem sum_6_68_4 : blockSum (rowCell 6) 68 4 ≤ (217491215246677295079311693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_68_2 sum_6_70_2 (by norm_num)

theorem sum_6_64_8 : blockSum (rowCell 6) 64 8 ≤ (82545036790079222833960493 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_64_4 sum_6_68_4 (by norm_num)

theorem sum_6_72_2 : blockSum (rowCell 6) 72 2 ≤ (116253119472400360678988831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_72) (by simpa only [blockSum_one] using cell_6_73) (by norm_num)

theorem sum_6_74_2 : blockSum (rowCell 6) 74 2 ≤ (120693741201443648458479773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_74) (by simpa only [blockSum_one] using cell_6_75) (by norm_num)

theorem sum_6_72_4 : blockSum (rowCell 6) 72 4 ≤ (59236715168461002284367151 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_72_2 sum_6_74_2 (by norm_num)

theorem sum_6_76_2 : blockSum (rowCell 6) 76 2 ≤ (124647986671587138964680137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_76) (by simpa only [blockSum_one] using cell_6_77) (by norm_num)

theorem sum_6_78_2 : blockSum (rowCell 6) 78 2 ≤ (4002305670716122478934879 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_78) (by simpa only [blockSum_one] using cell_6_79) (by norm_num)

theorem sum_6_76_4 : blockSum (rowCell 6) 76 4 ≤ (50544353626900611658119253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_76_2 sum_6_78_2 (by norm_num)

theorem sum_6_72_8 : blockSum (rowCell 6) 72 8 ≤ (489668628808347067428064869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_72_4 sum_6_76_4 (by norm_num)

theorem sum_6_64_16 : blockSum (rowCell 6) 64 16 ≤ (451196906379371590798933667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_64_8 sum_6_72_8 (by norm_num)

theorem sum_6_80_2 : blockSum (rowCell 6) 80 2 ≤ (65468443209756903875646893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_80) (by simpa only [blockSum_one] using cell_6_81) (by norm_num)

theorem sum_6_82_2 : blockSum (rowCell 6) 82 2 ≤ (133211382905210154310197417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_82) (by simpa only [blockSum_one] using cell_6_83) (by norm_num)

theorem sum_6_80_4 : blockSum (rowCell 6) 80 4 ≤ (264148269324723962061491203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_80_2 sum_6_82_2 (by norm_num)

theorem sum_6_84_2 : blockSum (rowCell 6) 84 2 ≤ (16859993362747193901744287 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_84) (by simpa only [blockSum_one] using cell_6_85) (by norm_num)

theorem sum_6_86_2 : blockSum (rowCell 6) 86 2 ≤ (33983478619113471199988983 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_86) (by simpa only [blockSum_one] using cell_6_87) (by norm_num)

theorem sum_6_84_4 : blockSum (rowCell 6) 84 4 ≤ (67703465344607859003477557 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_84_2 sum_6_86_2 (by norm_num)

theorem sum_6_80_8 : blockSum (rowCell 6) 80 8 ≤ (534962130703155398075401431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_80_4 sum_6_84_4 (by norm_num)

theorem sum_6_88_2 : blockSum (rowCell 6) 88 2 ≤ (6818657383727160231424661 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_88) (by simpa only [blockSum_one] using cell_6_89) (by norm_num)

theorem sum_6_90_2 : blockSum (rowCell 6) 90 2 ≤ (27241143125056521142572881 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_90) (by simpa only [blockSum_one] using cell_6_91) (by norm_num)

theorem sum_6_88_4 : blockSum (rowCell 6) 88 4 ≤ (2180630906398606482730861 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_88_2 sum_6_90_2 (by norm_num)

theorem sum_6_92_2 : blockSum (rowCell 6) 92 2 ≤ (135447410382478423524621379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_92) (by simpa only [blockSum_one] using cell_6_93) (by norm_num)

theorem sum_6_94_2 : blockSum (rowCell 6) 94 2 ≤ (134121120704599935546783737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_94) (by simpa only [blockSum_one] using cell_6_95) (by norm_num)

theorem sum_6_92_4 : blockSum (rowCell 6) 92 4 ≤ (67392132771769589767851279 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_92_2 sum_6_94_2 (by norm_num)

theorem sum_6_88_8 : blockSum (rowCell 6) 88 8 ≤ (542147394386904169412762741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_88_4 sum_6_92_4 (by norm_num)

theorem sum_6_80_16 : blockSum (rowCell 6) 80 16 ≤ (269277381272514891872041043 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_80_8 sum_6_88_8 (by norm_num)

theorem sum_6_64_32 : blockSum (rowCell 6) 64 32 ≤ (989751668924401374543015753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_64_16 sum_6_80_16 (by norm_num)

#print axioms sum_6_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
