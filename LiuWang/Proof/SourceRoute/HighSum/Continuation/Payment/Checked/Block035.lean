import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_96_0 : expNegUpper (269537482388332790811 / 3721127547115888000 : ℝ) ≤ (17440639155425323789038253679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (88051 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_96_1 : expNegUpper (1725600447495662292101 / 23815216301541683200 : ℝ) ≤ (681396670847102988799218199 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27521 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_96 : rowCell 2 96 ≤ (314248564037520145821159179 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17440639155425323789038253679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (681396670847102988799218199 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_96_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_96_1
  · norm_num [gridPoint]

theorem exp_2_97_0 : expNegUpper (4056262181557763149289 / 55980954490985164800 : ℝ) ≤ (34069805210014494335532111981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27521 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_97_1 : expNegUpper (10144075647965133066781 / 139952386227462912000 : ℝ) ≤ (33247289508798708642331226649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22021 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_97 : rowCell 2 97 ≤ (4908823027098145194882845077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34069805210014494335532111981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33247289508798708642331226649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_97_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_97_1
  · norm_num [gridPoint]

theorem exp_2_98_0 : expNegUpper (30657088696857023242567 / 422959451240675584000 : ℝ) ≤ (33247262265321603930571316197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22021 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_98_1 : expNegUpper (61335603445980662635653 / 845918902481351168000 : ℝ) ≤ (32415726631645099968567104303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_98 : rowCell 2 98 ≤ (2394102072229199583424104003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33247262265321603930571316197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (32415726631645099968567104303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_98_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_98_1
  · norm_num [gridPoint]

theorem exp_2_99_0 : expNegUpper (98859424093388783373 / 1363434121445888000 : ℝ) ≤ (8103925114270564262188630323 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_99_1 : expNegUpper (24723789731702567863 / 340858530361472000 : ℝ) ≤ (15788570232124164834000074793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176239 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_99 : rowCell 2 99 ≤ (933283090710288328266950787 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8103925114270564262188630323 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15788570232124164834000074793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_99_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_99_1
  · norm_num [gridPoint]

theorem exp_2_100_0 : expNegUpper (5188569225805576944781 / 71533048969313664000 : ℝ) ≤ (3947139417180741388287893093 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176239 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_100_1 : expNegUpper (20762025509985572065097 / 286132195877254656000 : ℝ) ≤ (3073346563333173829871219059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (881381 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_100 : rowCell 2 100 ≤ (2271871773275849293038037161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3947139417180741388287893093 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3073346563333173829871219059 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_100_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_100_1
  · norm_num [gridPoint]

theorem exp_2_101_0 : expNegUpper (62741259339949494401939 / 864669687665603072000 : ℝ) ≤ (3841680191507875251193400927 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_101_1 : expNegUpper (6276542004042019897809 / 86466968766560307200 : ℝ) ≤ (14943285465086294154125951533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1763147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_101 : rowCell 2 101 ≤ (1105116443009666446440521821 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3841680191507875251193400927 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14943285465086294154125951533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_101_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_101_1
  · norm_num [gridPoint]

theorem exp_2_102_0 : expNegUpper (6322243594155434953089 / 87096562600519731200 : ℝ) ≤ (29886547831265725462847137871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1763147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_102_1 : expNegUpper (63247514852985514734961 / 870965626005197312000 : ℝ) ≤ (725956374680734880267212829 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220443 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_102 : rowCell 2 102 ≤ (4296849561777196441224199803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29886547831265725462847137871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (725956374680734880267212829 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_102_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_102_1
  · norm_num [gridPoint]

theorem exp_2_103_0 : expNegUpper (3033636690800958831109 / 41775447745264128000 : ℝ) ≤ (5807646573338309654761387961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220443 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_103_1 : expNegUpper (379359350952329227351 / 5221930968158016000 : ℝ) ≤ (28190242532289724177294654997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_103 : rowCell 2 103 ≤ (52164398028776008242141201 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5807646573338309654761387961 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28190242532289724177294654997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_103_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_103_1
  · norm_num [gridPoint]

theorem exp_2_104_0 : expNegUpper (320965365140427494491 / 4418130088008256000 : ℝ) ≤ (28190221365426525641290409777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_104_1 : expNegUpper (2568799934151049283487 / 35345040704066048000 : ℝ) ≤ (13672090604347635604898990839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441093 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_104 : rowCell 2 104 ≤ (809923705978954822786644781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28190221365426525641290409777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13672090604347635604898990839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_104_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_104_1
  · norm_num [gridPoint]

theorem exp_2_105_0 : expNegUpper (64682553497689086594687 / 889990470858510848000 : ℝ) ≤ (27344160970225716145404827331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441093 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_105_1 : expNegUpper (32355203513339463570323 / 444995235429255424000 : ℝ) ≤ (3312704868376537292142071023 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441201 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_105 : rowCell 2 105 ≤ (196324205352542957979777761 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27344160970225716145404827331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3312704868376537292142071023 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_105_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_105_1
  · norm_num [gridPoint]

theorem exp_2_106_0 : expNegUpper (10862470317994924211969 / 149396293736854272000 : ℝ) ≤ (3312702451397334315010839499 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441201 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_106_1 : expNegUpper (4346907131402536138963 / 59758517494741708800 : ℝ) ≤ (1026564074826510657213870453 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_106 : rowCell 2 106 ≤ (237748204881016982251575817 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3312702451397334315010839499 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1026564074826510657213870453 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_106_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_106_1
  · norm_num [gridPoint]

theorem exp_2_107_0 : expNegUpper (13133977650253104331729 / 180557578457899110400 : ℝ) ≤ (12832041705667717141287737521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765247 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_107_1 : expNegUpper (16424902044798055911909 / 225696973072373888000 : ℝ) ≤ (24832972715515052769943510533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_107 : rowCell 2 107 ≤ (920572675304700370776036419 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12832041705667717141287737521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24832972715515052769943510533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_107_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_107_1
  · norm_num [gridPoint]

theorem exp_2_108_0 : expNegUpper (16541940629978915621061 / 227305215115905152000 : ℝ) ≤ (6208238776572978366441627093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1765701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_108_1 : expNegUpper (66198420643480118559283 / 909220860463620608000 : ℝ) ≤ (24009569741249876972157438693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883083 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_108 : rowCell 2 108 ≤ (3561640793838665072060760793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6208238776572978366441627093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24009569741249876972157438693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_108_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_108_1
  · norm_num [gridPoint]

theorem exp_2_109_0 : expNegUpper (888912729416781526369 / 12209022225913344000 : ℝ) ≤ (6002388238887602658792774643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883083 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_109_1 : expNegUpper (444667029041602490323 / 6104511112956672000 : ℝ) ≤ (11597563055230452677471488899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_109 : rowCell 2 109 ≤ (1721103803973696765770414159 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6002388238887602658792774643 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11597563055230452677471488899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_109_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_109_1
  · norm_num [gridPoint]

theorem exp_2_110_0 : expNegUpper (4797998200188073169143 / 65868236552081152000 : ℝ) ≤ (11597555060807351089967164917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883321 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_110_1 : expNegUpper (9600645615687376477743 / 131736473104162304000 : ℝ) ≤ (22390789709911693201023821853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_110 : rowCell 2 110 ≤ (3324164771796784638175318501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11597555060807351089967164917 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22390789709911693201023821853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_110_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_110_1
  · norm_num [gridPoint]

theorem exp_2_111_0 : expNegUpper (67678332801377538884289 / 928656794820526592000 : ℝ) ≤ (5597693622810359620438299321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_111_1 : expNegUpper (169279563741331376689 / 2321641987051316480 : ℝ) ≤ (6749257308481259303557477 / 312500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_111 : rowCell 2 111 ≤ (3207673494117795523369142737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5597693622810359620438299321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6749257308481259303557477 / 312500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_111_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_111_1
  · norm_num [gridPoint]

theorem exp_2_112_0 : expNegUpper (1832998352011580773 / 25139277317679360 : ℝ) ≤ (172780871296311513100653463 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_112_1 : expNegUpper (733569708696148024427 / 10055710927071744000 : ℝ) ≤ (10408302787332103929649045671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221017 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_112 : rowCell 2 112 ≤ (1546441313445610688185551573 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172780871296311513100653463 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10408302787332103929649045671 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_112_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_112_1
  · norm_num [gridPoint]

theorem exp_2_113_0 : expNegUpper (68699602475331468710999 / 941728275920572928000 : ℝ) ≤ (832663672666717659716898951 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221017 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_113_1 : expNegUpper (34367500769388964430799 / 470864137960286464000 : ℝ) ≤ (4009726254677672445265519731 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (353731 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_113 : rowCell 2 113 ≤ (1489964391287887819834044023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (832663672666717659716898951 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4009726254677672445265519731 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_113_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_113_1
  · norm_num [gridPoint]

theorem exp_2_114_0 : expNegUpper (1384290682704363549591 / 18965965478584576000 : ℝ) ≤ (10024309103120738217118838489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (353731 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_114_1 : expNegUpper (2770035655159187406973 / 37931930957169152000 : ℝ) ≤ (385890267328190176274977939 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (353837 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_114 : rowCell 2 114 ≤ (2868936501622482147902739709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10024309103120738217118838489 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (385890267328190176274977939 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_114_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_114_1
  · norm_num [gridPoint]

theorem exp_2_115_0 : expNegUpper (23244114555609859263439 / 318297036747879936000 : ℝ) ≤ (19294500964126530102833102771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (353837 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_115_1 : expNegUpper (5814138535140473494913 / 79574259186969984000 : ℝ) ≤ (4638746058569962087375615919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884863 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_115 : rowCell 2 115 ≤ (690004616516162764993737569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19294500964126530102833102771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4638746058569962087375615919 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_115_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_115_1
  · norm_num [gridPoint]

theorem exp_2_116_0 : expNegUpper (17563260265626079093091 / 240376696215951488000 : ℝ) ≤ (9277486235600539562453409863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (884863 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_116_1 : expNegUpper (14058264931846913176911 / 192301356972761190400 : ℝ) ≤ (4457674410714003148759333071 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442569 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_116 : rowCell 2 116 ≤ (1326637877483768113193334851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9277486235600539562453409863 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4457674410714003148759333071 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_116_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_116_1
  · norm_num [gridPoint]

theorem exp_2_117_0 : expNegUpper (2022189608988029712993 / 27661294222563635200 : ℝ) ≤ (8915343246849099423169654683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442569 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_117_1 : expNegUpper (5058277720283213124299 / 69153235556409088000 : ℝ) ≤ (17122230875153390330700975879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1770837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_117 : rowCell 2 117 ≤ (159299883596772278774339303 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8915343246849099423169654683 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17122230875153390330700975879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_117_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_117_1
  · norm_num [gridPoint]

theorem exp_2_118_0 : expNegUpper (11883856569233065877759 / 162467774836900608000 : ℝ) ≤ (2140277539381925033242861653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1770837 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_118_1 : expNegUpper (23781120896071860744971 / 324935549673801216000 : ℝ) ≤ (657203483163972080023928053 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110713 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_118 : rowCell 2 118 ≤ (2446664399832935325141494211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2140277539381925033242861653 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (657203483163972080023928053 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_118_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_118_1
  · norm_num [gridPoint]

theorem exp_2_119_0 : expNegUpper (2873302414291801161473 / 39259633542353408000 : ℝ) ≤ (16430077083662980630205881961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (110713 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_119_1 : expNegUpper (359368792321625040489 / 4907454192794176000 : ℝ) ≤ (1575469780372431824373232191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1771989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_119 : rowCell 2 119 ≤ (2346942700796969720913905881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16430077083662980630205881961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1575469780372431824373232191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_119_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_119_1
  · norm_num [gridPoint]

theorem exp_2_120_0 : expNegUpper (9045613641576198499329 / 123524733300252736000 : ℝ) ≤ (3150937669810139302842230863 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1771989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_120_1 : expNegUpper (72407085404631908057911 / 988197866402021888000 : ℝ) ≤ (15096425697127257781106113677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (88629 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_120 : rowCell 2 120 ≤ (1124845477022536145110173691 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3150937669810139302842230863 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15096425697127257781106113677 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_120_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_120_1
  · norm_num [gridPoint]

theorem exp_2_121_0 : expNegUpper (24300065244560239623013 / 331642577516987904000 : ℝ) ≤ (7548208379924153065505676411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (88629 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_121_1 : expNegUpper (2431445116715830961477 / 33164257751698790400 : ℝ) ≤ (3613891835119364051184191263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_121 : rowCell 2 121 ≤ (26936965390080871574373141 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7548208379924153065505676411 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3613891835119364051184191263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_121_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_121_1
  · norm_num [gridPoint]

theorem exp_2_122_0 : expNegUpper (7343843015284706838911 / 100168043700566067200 : ℝ) ≤ (14455558897783581489882941927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773181 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_122_1 : expNegUpper (73482572747192717186061 / 1001680437005660672000 : ℝ) ≤ (6916178096679658591979046233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_122 : rowCell 2 122 ≤ (2062780183369854869994515507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14455558897783581489882941927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6916178096679658591979046233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_122_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_122_1
  · norm_num [gridPoint]

theorem exp_2_123_0 : expNegUpper (73979622382447283283909 / 1008455979766112768000 : ℝ) ≤ (2766469644604561785687627461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1773791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_123_1 : expNegUpper (18506188283530979953057 / 252113994941528192000 : ℝ) ≤ (6613482813450539387501190543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443603 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_123 : rowCell 2 123 ≤ (1973189477038736932327741161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2766469644604561785687627461 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6613482813450539387501190543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_123_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_123_1
  · norm_num [gridPoint]

theorem exp_2_124_0 : expNegUpper (1419500617425143053 / 19338178301568000 : ℝ) ≤ (529078324291828631476312661 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (443603 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_124_1 : expNegUpper (5681516545112928263 / 77352713206272000 : ℝ) ≤ (1579939002793124911907587719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1775041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_124 : rowCell 2 124 ≤ (1886206241260158042871684989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (529078324291828631476312661 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1579939002793124911907587719 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_124_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_124_1
  · norm_num [gridPoint]

theorem exp_2_125_0 : expNegUpper (75070920242303896113947 / 1022075580204282368000 : ℝ) ≤ (1579938116557753872651817663 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1775041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_125_1 : expNegUpper (37559018650490577417033 / 511037790102141184000 : ℝ) ≤ (12070057913993454324335157729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1775681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_125 : rowCell 2 125 ≤ (1801843522761403850830763259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1579938116557753872651817663 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12070057913993454324335157729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_125_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_125_1
  · norm_num [gridPoint]

theorem exp_2_126_0 : expNegUpper (37810522928618793753657 / 514459818940999936000 : ℝ) ≤ (2414010246690834537263509673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1775681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_126_1 : expNegUpper (15133832213116896137573 / 205783927576399974400 : ℝ) ≤ (2879653789197325811935992307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (177633 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_126 : rowCell 2 126 ≤ (430026686529753562371168843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2414010246690834537263509673 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2879653789197325811935992307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_126_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_126_1
  · norm_num [gridPoint]

theorem exp_2_127_0 : expNegUpper (5078277950130648746111 / 69052435591031500800 : ℝ) ≤ (575930443292721084506473073 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (177633 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_127_1 : expNegUpper (198498140470718249329 / 2697360765274668000 : ℝ) ≤ (10985148100144861006282327447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (444247 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_127 : rowCell 2 127 ≤ (328198835235963366840579041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (575930443292721084506473073 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10985148100144861006282327447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_127_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_127_1
  · norm_num [gridPoint]

theorem sum_2_96_2 : blockSum (rowCell 2) 96 2 ≤ (9936800051698467528021391941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_96) (by simpa only [blockSum_one] using cell_2_97) (by norm_num)

theorem sum_2_98_2 : blockSum (rowCell 2) 98 2 ≤ (9454619598009840808182961941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_98) (by simpa only [blockSum_one] using cell_2_99) (by norm_num)

theorem sum_2_96_4 : blockSum (rowCell 2) 96 4 ≤ (9695709824854154168102176941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_96_2 sum_2_98_2 (by norm_num)

theorem sum_2_100_2 : blockSum (rowCell 2) 100 2 ≤ (4482104659295182185919080803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_100) (by simpa only [blockSum_one] using cell_2_101) (by norm_num)

theorem sum_2_102_2 : blockSum (rowCell 2) 102 2 ≤ (8470001404079277100595495883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_102) (by simpa only [blockSum_one] using cell_2_103) (by norm_num)

theorem sum_2_100_4 : blockSum (rowCell 2) 100 4 ≤ (17434210722669641472433657489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_100_2 sum_2_102_2 (by norm_num)

theorem sum_2_96_8 : blockSum (rowCell 2) 96 8 ≤ (36825630372377949808638011371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_96_4 sum_2_100_4 (by norm_num)

theorem sum_2_104_2 : blockSum (rowCell 2) 104 2 ≤ (63808821095565066188230233 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_104) (by simpa only [blockSum_one] using cell_2_105) (by norm_num)

theorem sum_2_106_2 : blockSum (rowCell 2) 106 2 ≤ (1871565494828768299782339687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_106) (by simpa only [blockSum_one] using cell_2_107) (by norm_num)

theorem sum_2_104_4 : blockSum (rowCell 2) 104 4 ≤ (15462364616260706472658137873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_104_2 sum_2_106_2 (by norm_num)

theorem sum_2_108_2 : blockSum (rowCell 2) 108 2 ≤ (7003848401786058603601589111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_108) (by simpa only [blockSum_one] using cell_2_109) (by norm_num)

theorem sum_2_110_2 : blockSum (rowCell 2) 110 2 ≤ (3265919132957290080772230619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_110) (by simpa only [blockSum_one] using cell_2_111) (by norm_num)

theorem sum_2_108_4 : blockSum (rowCell 2) 108 4 ≤ (13535686667700638765146050349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_108_2 sum_2_110_2 (by norm_num)

theorem sum_2_104_8 : blockSum (rowCell 2) 104 8 ≤ (14499025641980672618902094111 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_104_4 sum_2_108_4 (by norm_num)

theorem sum_2_96_16 : blockSum (rowCell 2) 96 16 ≤ (65823681656339295046442199593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_96_8 sum_2_104_8 (by norm_num)

theorem sum_2_112_2 : blockSum (rowCell 2) 112 2 ≤ (759101426183374627004898899 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_112) (by simpa only [blockSum_one] using cell_2_113) (by norm_num)

theorem sum_2_114_2 : blockSum (rowCell 2) 114 2 ≤ (1125790993537426641575537997 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_114) (by simpa only [blockSum_one] using cell_2_115) (by norm_num)

theorem sum_2_112_4 : blockSum (rowCell 2) 112 4 ≤ (11701766377154130223916881177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_112_2 sum_2_114_2 (by norm_num)

theorem sum_2_116_2 : blockSum (rowCell 2) 116 2 ≤ (104041477850317853735521971 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_116) (by simpa only [blockSum_one] using cell_2_117) (by norm_num)

theorem sum_2_118_2 : blockSum (rowCell 2) 118 2 ≤ (1198401775157476261513850023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_118) (by simpa only [blockSum_one] using cell_2_119) (by norm_num)

theorem sum_2_116_4 : blockSum (rowCell 2) 116 4 ≤ (4997840496572898866415749321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_116_2 sum_2_118_2 (by norm_num)

theorem sum_2_112_8 : blockSum (rowCell 2) 112 8 ≤ (21697447370299927956748379819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_112_4 sum_2_116_4 (by norm_num)

theorem sum_2_120_2 : blockSum (rowCell 2) 120 2 ≤ (2202324092625771008085099331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_120) (by simpa only [blockSum_one] using cell_2_121) (by norm_num)

theorem sum_2_122_2 : blockSum (rowCell 2) 122 2 ≤ (1008992415102147950580564167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_122) (by simpa only [blockSum_one] using cell_2_123) (by norm_num)

theorem sum_2_120_4 : blockSum (rowCell 2) 120 4 ≤ (844061784566013381849245533 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_120_2 sum_2_122_2 (by norm_num)

theorem sum_2_124_2 : blockSum (rowCell 2) 124 2 ≤ (461006220502695236712806031 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_124) (by simpa only [blockSum_one] using cell_2_125) (by norm_num)

theorem sum_2_126_2 : blockSum (rowCell 2) 126 2 ≤ (3361100922298831083687570577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_126) (by simpa only [blockSum_one] using cell_2_127) (by norm_num)

theorem sum_2_124_4 : blockSum (rowCell 2) 124 4 ≤ (281966027452815719095600753 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_124_2 sum_2_126_2 (by norm_num)

theorem sum_2_120_8 : blockSum (rowCell 2) 120 8 ≤ (3097953706396105359176494831 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_120_4 sum_2_124_4 (by norm_num)

theorem sum_2_112_16 : blockSum (rowCell 2) 112 16 ≤ (18593607951140227376315426987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_112_8 sum_2_120_8 (by norm_num)

theorem sum_2_96_32 : blockSum (rowCell 2) 96 32 ≤ (103010897558619749799073053567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_96_16 sum_2_112_16 (by norm_num)

#print axioms sum_2_96_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
