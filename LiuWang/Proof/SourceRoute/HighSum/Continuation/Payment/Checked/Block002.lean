import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_64_0 : expNegUpper (3007592018771262327 / 44984395697672000 : ℝ) ≤ (2301809855168300581763085470189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337191 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_64_1 : expNegUpper (192517408764013237167 / 2879001324651008000 : ℝ) ≤ (364279501159117704861499546371 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_64 : rowCell 0 64 ≤ (267097976671367313370342038331 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2301809855168300581763085470189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (364279501159117704861499546371 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_64_1
  · norm_num [gridPoint]

theorem exp_0_65_0 : expNegUpper (43680918161884987812167 / 653226219073131008000 : ℝ) ≤ (1138372098924590262093053171363 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_65_1 : expNegUpper (21844402517799469817703 / 326613109536565504000 : ℝ) ≤ (4498841389449893427416107542707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (843129 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_65 : rowCell 0 65 ≤ (1320208041771104121018729804213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1138372098924590262093053171363 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4498841389449893427416107542707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_65_1
  · norm_num [gridPoint]

theorem exp_0_66_0 : expNegUpper (22027449750297399966807 / 329349989202770176000 : ℝ) ≤ (8997672346141737590030092814297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (843129 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_66_1 : expNegUpper (8812716935441090327201 / 131739995681108070400 : ℝ) ≤ (4439906888131772928646133245651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52701 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_66 : rowCell 0 66 ≤ (1303642349849731367475593644247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8997672346141737590030092814297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4439906888131772928646133245651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_66_1
  · norm_num [gridPoint]

theorem exp_0_67_0 : expNegUpper (987361757306094680049 / 14759923912082329600 : ℝ) ≤ (8879803650231541556981719817189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (52701 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_67_1 : expNegUpper (1234465719140587808151 / 18449904890102912000 : ℝ) ≤ (8753873681901592297082136030193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84331 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_67 : rowCell 0 67 ≤ (1285863593816126209000783378887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8879803650231541556981719817189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8753873681901592297082136030193 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_67_1
  · norm_num [gridPoint]

theorem exp_0_68_0 : expNegUpper (11202516722190504136751 / 167429002996906112000 : ℝ) ≤ (350154554547331781918386306129 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84331 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_68_1 : expNegUpper (44820358663504714736763 / 669716011987624448000 : ℝ) ≤ (8620368350508768472181963408287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_68 : rowCell 0 68 ≤ (633472311360320086805173333147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (350154554547331781918386306129 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8620368350508768472181963408287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_68_1
  · norm_num [gridPoint]

theorem exp_0_69_0 : expNegUpper (1807650916915868579883 / 27010331449491968000 : ℝ) ≤ (4310179420205886056816930727283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_69_1 : expNegUpper (904047459857495185901 / 13505165724745984000 : ℝ) ≤ (4239906741148862630537258038547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_69 : rowCell 0 69 ≤ (1246959929208047732877782479167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4310179420205886056816930727283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4239906741148862630537258038547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_69_1
  · norm_num [gridPoint]

theorem exp_0_70_0 : expNegUpper (2531939287417611176749 / 37823522155151616000 : ℝ) ≤ (8479804279886520200062859638073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_70_1 : expNegUpper (5065202096612215721929 / 75647044310303232000 : ℝ) ≤ (8332731844456021872812385494001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (168727 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_70 : rowCell 0 70 ≤ (306496309799995595489176618471 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8479804279886520200062859638073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8332731844456021872812385494001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_70_1
  · norm_num [gridPoint]

theorem exp_0_71_0 : expNegUpper (45960979632961523329289 / 686411349653914112000 : ℝ) ≤ (333308917943617651465793026213 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (168727 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_71_1 : expNegUpper (1149342657143722701819 / 17160283741347852800 : ℝ) ≤ (4089825289102268683699163917413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337503 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_71 : rowCell 0 71 ≤ (602048556454740161658230622199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (333308917943617651465793026213 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4089825289102268683699163917413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_71_1
  · norm_num [gridPoint]

theorem exp_0_72_0 : expNegUpper (1158737507339223191739 / 17300553470521356800 : ℝ) ≤ (4089820993539686859203802855453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337503 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_72_1 : expNegUpper (46363045233930305750311 / 692022138820854272000 : ℝ) ≤ (4010549302829217436706147312559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_72 : rowCell 0 72 ≤ (236274511875063458078082769139 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4089820993539686859203802855453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4010549302829217436706147312559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_72_1
  · norm_num [gridPoint]

theorem exp_0_73_0 : expNegUpper (5193386571964206770151 / 77517307365949952000 : ℝ) ≤ (802109031684391844167904506099 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687773 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_73_1 : expNegUpper (2597491428132932292171 / 38758653682974976000 : ℝ) ≤ (1571520829812774052734884366873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422011 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_73 : rowCell 0 73 ≤ (231577733293711033284657954403 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (802109031684391844167904506099 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1571520829812774052734884366873 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_73_1
  · norm_num [gridPoint]

theorem exp_0_74_0 : expNegUpper (301657127600812607 / 4501198285260800 : ℝ) ≤ (785759615954671971943679395019 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422011 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_74_1 : expNegUpper (603508706502079761 / 9002396570521600 : ℝ) ≤ (3844846186672396276858504095349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_74 : rowCell 0 74 ≤ (1133722248085490344676433163733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (785759615954671971943679395019 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3844846186672396276858504095349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_74_1
  · norm_num [gridPoint]

theorem exp_0_75_0 : expNegUpper (47529851405754901135797 / 708991536156205568000 : ℝ) ≤ (307587387182782527138635593871 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688329 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_75_1 : expNegUpper (11886467798378888171629 / 177247884039051392000 : ℝ) ≤ (93973539515777206402050105277 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_75 : rowCell 0 75 ≤ (110894951000268245550686048207 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (307587387182782527138635593871 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93973539515777206402050105277 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_75_1
  · norm_num [gridPoint]

theorem exp_0_76_0 : expNegUpper (1331340688733341709349 / 19852602181837952000 : ℝ) ≤ (1503575151834529756830170743801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688627 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_76_1 : expNegUpper (1065447026507847601407 / 15882081745470361600 : ℝ) ≤ (1468537805775813247379040982263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (844469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_76 : rowCell 0 76 ≤ (135455716954175978068424102049 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1503575151834529756830170743801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1468537805775813247379040982263 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_76_1
  · norm_num [gridPoint]

theorem exp_0_77_0 : expNegUpper (9665835269180363555023 / 144083731848376422400 : ℝ) ≤ (1835670478489858845401137665609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (844469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_77_1 : expNegUpper (24173431342913198093793 / 360209329620941056000 : ℝ) ≤ (7164613187453587999725441393833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (844631 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_77 : rowCell 0 77 ≤ (132235624086622542591222148051 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1835670478489858845401137665609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7164613187453587999725441393833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_77_1
  · norm_num [gridPoint]

theorem exp_0_78_0 : expNegUpper (24366298026299048290257 / 363083239121676544000 : ℝ) ≤ (7164606354769233540468274930367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (844631 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_78_1 : expNegUpper (48751120664773961788393 / 726166478243353088000 : ℝ) ≤ (6984147756361739444255109162113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689599 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_78 : rowCell 0 78 ≤ (25793496538873556731989253261 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7164606354769233540468274930367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6984147756361739444255109162113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_78_1
  · norm_num [gridPoint]

theorem exp_0_79_0 : expNegUpper (218393484030345709697 / 3253053935780352000 : ℝ) ≤ (1746035300149843139621525805947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689599 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_79_1 : expNegUpper (13654972256120690443 / 203315870986272000 : ℝ) ≤ (6801772130193808990659054790567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_79 : rowCell 0 79 ≤ (100528118586294693306271298251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1746035300149843139621525805947 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6801772130193808990659054790567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_79_1
  · norm_num [gridPoint]

theorem exp_0_80_0 : expNegUpper (3096687493808095550507 / 46108164447722528000 : ℝ) ≤ (1360353169140162877091294826719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422487 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_80_1 : expNegUpper (49567211049946614335871 / 737730631163560448000 : ℝ) ≤ (3308975750891323494531093024797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (169031 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_80 : rowCell 0 80 ≤ (978577845755798383102229369667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1360353169140162877091294826719 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3308975750891323494531093024797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_80_1
  · norm_num [gridPoint]

theorem exp_0_81_0 : expNegUpper (1611548517007805667369 / 23985385970396672000 : ℝ) ≤ (3308972741302727436129564235061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (169031 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_81_1 : expNegUpper (161222785293061273357 / 2398538597039667200 : ℝ) ≤ (1608283885404257825793115392273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422671 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_81 : rowCell 0 81 ≤ (951696553866911391802394784979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3308972741302727436129564235061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1608283885404257825793115392273 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_81_1
  · norm_num [gridPoint]

theorem exp_0_82_0 : expNegUpper (559683958645597467243 / 8326512636742092800 : ℝ) ≤ (257325191261534947180391624651 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422671 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_82_1 : expNegUpper (5599274143008919282029 / 83265126367420928000 : ℝ) ≤ (249910289315032874773116482189 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (169107 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_82 : rowCell 0 82 ≤ (924701674075510152175058687643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (257325191261534947180391624651 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (249910289315032874773116482189 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_82_1
  · norm_num [gridPoint]

theorem exp_0_83_0 : expNegUpper (50787666645853564627469 / 755248147837035008000 : ℝ) ≤ (6247751725450745685376864148269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (169107 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_83_1 : expNegUpper (12702608145244774364427 / 188812036959258752000 : ℝ) ≤ (3031115930096877906316618670569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691469 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_83 : rowCell 0 83 ≤ (897655062816074776716711219059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6247751725450745685376864148269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3031115930096877906316618670569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_83_1
  · norm_num [gridPoint]

theorem exp_0_84_0 : expNegUpper (512063451228300001443 / 7611329966730368000 : ℝ) ≤ (3031113299392141639418812963501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691469 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_84_1 : expNegUpper (2049198772595364529123 / 30445319866921472000 : ℝ) ≤ (1175391229848287171102233432829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_84 : rowCell 0 84 ≤ (870615932595535618633748758701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3031113299392141639418812963501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1175391229848287171102233432829 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_84_1
  · norm_num [gridPoint]

theorem exp_0_85_0 : expNegUpper (5736400189041302814603 / 85226742646088192000 : ℝ) ≤ (1469237781762444868531305575843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_85_1 : expNegUpper (2869560415618553754357 / 42613371323044096000 : ℝ) ≤ (1423076888318198312326529244299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1692301 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_85 : rowCell 0 85 ≤ (843640737224967605304044468183 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1469237781762444868531305575843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1423076888318198312326529244299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_85_1
  · norm_num [gridPoint]

theorem exp_0_86_0 : expNegUpper (26025723186908693458957 / 386485604631152896000 : ℝ) ≤ (2846151381686524787673624539227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1692301 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_86_1 : expNegUpper (2083071882882692289513 / 30918848370492231680 : ℝ) ≤ (2754321840982139854754038778679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (338547 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_86 : rowCell 0 86 ≤ (816783078144320034208429780491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2846151381686524787673624539227 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2754321840982139854754038778679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_86_1
  · norm_num [gridPoint]

theorem exp_0_87_0 : expNegUpper (2099115565300225265313 / 31156982920622919680 : ℝ) ≤ (2754319558666270793075687912101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (338547 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_87_1 : expNegUpper (6563013510002847366917 / 97365571626946624000 : ℝ) ≤ (5326301867141310214230920305319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84659 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_87 : rowCell 0 87 ≤ (395046815552562005755051969867 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2754319558666270793075687912101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5326301867141310214230920305319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_87_1
  · norm_num [gridPoint]

theorem exp_0_88_0 : expNegUpper (734818610691320919517 / 10901399653813824000 : ℝ) ≤ (332893595042759505479396016229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (84659 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_88_1 : expNegUpper (5881558944148781044447 / 87211197230510592000 : ℝ) ≤ (5145598859358024868402809155767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423409 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_88 : rowCell 0 88 ≤ (38181004618853974389010636783 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (332893595042759505479396016229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5145598859358024868402809155767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_88_1
  · norm_num [gridPoint]

theorem exp_0_89_0 : expNegUpper (2133544355118578294567 / 31635992617574912000 : ℝ) ≤ (2572797361969664873955452758503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (423409 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_89_1 : expNegUpper (1067331486327094107219 / 15817996308787456000 : ℝ) ≤ (4966830648764290860323321320021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (211763 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_89 : rowCell 0 89 ≤ (147481428711943760632316006279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2572797361969664873955452758503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4966830648764290860323321320021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_89_1
  · norm_num [gridPoint]

theorem exp_0_90_0 : expNegUpper (26886452924706165919371 / 398460847054952704000 : ℝ) ≤ (2483413358615200254244954131591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (211763 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_90_1 : expNegUpper (53801749529408453547181 / 796921694109905408000 : ℝ) ≤ (4790272403256204144962434832711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1694583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_90 : rowCell 0 90 ≤ (711496434009624273513613194643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2483413358615200254244954131591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4790272403256204144962434832711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_90_1
  · norm_num [gridPoint]

theorem exp_0_91_0 : expNegUpper (6023315652939708484221 / 89218490120688128000 : ℝ) ≤ (4790268668459386134983671343473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1694583 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_91_1 : expNegUpper (301330922937994003821 / 4460924506034406400 : ℝ) ≤ (4616178516559615268229930417131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_91 : rowCell 0 91 ≤ (85740822479559796603926130013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4790268668459386134983671343473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4616178516559615268229930417131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_91_1
  · norm_num [gridPoint]

theorem exp_0_92_0 : expNegUpper (2732471197571911882549 / 40451698318411801600 : ℝ) ≤ (923234994275970323085695118159 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847537 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_92_1 : expNegUpper (54680034106984753511811 / 809033966368236032000 : ℝ) ≤ (4444782758636204172838904003843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67823 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_92 : rowCell 0 92 ≤ (132146635675396269876115918303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (923234994275970323085695118159 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4444782758636204172838904003843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_92_1
  · norm_num [gridPoint]

theorem exp_0_93_0 : expNegUpper (55091665066693562446779 / 815124359956034048000 : ℝ) ≤ (2222389698000658166372615017063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (67823 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_93_1 : expNegUpper (27561581728092299374169 / 407562179978017024000 : ℝ) ≤ (4276298520623648832609451075983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1696087 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_93 : rowCell 0 93 ≤ (39746802313983323599987755931 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2222389698000658166372615017063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4276298520623648832609451075983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_93_1
  · norm_num [gridPoint]

theorem exp_0_94_0 : expNegUpper (123414609365693327721 / 1824972426332416000 : ℝ) ≤ (1069073833381945740988712832249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1696087 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_94_1 : expNegUpper (246973174083453791673 / 3649944852664832000 : ℝ) ≤ (2055459573210166071614717068491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1696609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_94 : rowCell 0 94 ≤ (611603215265825882000544707061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1069073833381945740988712832249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2055459573210166071614717068491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_94_1
  · norm_num [gridPoint]

theorem exp_0_95_0 : expNegUpper (55984161387382189463057 / 827373662048895488000 : ℝ) ≤ (2055458063970418337845318303967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1696609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_95_1 : expNegUpper (1750545194909403542973 / 25855426939027984000 : ℝ) ≤ (987204585748835894217903458383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1697143 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_95 : rowCell 0 95 ≤ (587723078788354995741284963589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2055458063970418337845318303967 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (987204585748835894217903458383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_95_1
  · norm_num [gridPoint]

theorem sum_0_64_2 : blockSum (rowCell 0) 64 2 ≤ (663924481281985171967609998967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_64) (by simpa only [blockSum_one] using cell_0_65) (by norm_num)

theorem sum_0_66_2 : blockSum (rowCell 0) 66 2 ≤ (1294752971832928788238188511567 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_66) (by simpa only [blockSum_one] using cell_0_67) (by norm_num)

theorem sum_0_64_4 : blockSum (rowCell 0) 64 4 ≤ (2622601934396899132173408509501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_64_2 sum_0_66_2 (by norm_num)

theorem sum_0_68_2 : blockSum (rowCell 0) 68 2 ≤ (2513904551928687906488129145461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_68) (by simpa only [blockSum_one] using cell_0_69) (by norm_num)

theorem sum_0_70_2 : blockSum (rowCell 0) 70 2 ≤ (1215041176054731352636583859141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_70) (by simpa only [blockSum_one] using cell_0_71) (by norm_num)

theorem sum_0_68_4 : blockSum (rowCell 0) 68 4 ≤ (4943986904038150611761296863743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_68_2 sum_0_70_2 (by norm_num)

theorem sum_0_64_8 : blockSum (rowCell 0) 64 8 ≤ (2037838154566389775221622776549 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_64_4 sum_0_68_4 (by norm_num)

theorem sum_0_72_2 : blockSum (rowCell 0) 72 2 ≤ (233926122584387245681370361771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_72) (by simpa only [blockSum_one] using cell_0_73) (by norm_num)

theorem sum_0_74_2 : blockSum (rowCell 0) 74 2 ≤ (2242671758088172800183293645803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_74) (by simpa only [blockSum_one] using cell_0_75) (by norm_num)

theorem sum_0_72_4 : blockSum (rowCell 0) 72 4 ≤ (4581932983932045256996997263513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_72_2 sum_0_74_2 (by norm_num)

theorem sum_0_76_2 : blockSum (rowCell 0) 76 2 ≤ (2676913410407985206596462501 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_76) (by simpa only [blockSum_one] using cell_0_77) (by norm_num)

theorem sum_0_78_2 : blockSum (rowCell 0) 78 2 ≤ (40740420948357784046845662259 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_78) (by simpa only [blockSum_one] using cell_0_79) (by norm_num)

theorem sum_0_76_4 : blockSum (rowCell 0) 76 4 ≤ (3342841420595421894095562491 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_76_2 sum_0_78_2 (by norm_num)

theorem sum_0_72_8 : blockSum (rowCell 0) 72 8 ≤ (8760484759676322624616450377263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_72_4 sum_0_76_4 (by norm_num)

theorem sum_0_64_16 : blockSum (rowCell 0) 64 16 ≤ (2368709441563533937590570532501 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_64_8 sum_0_72_8 (by norm_num)

theorem sum_0_80_2 : blockSum (rowCell 0) 80 2 ≤ (965137199811354887452312077323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_80) (by simpa only [blockSum_one] using cell_0_81) (by norm_num)

theorem sum_0_82_2 : blockSum (rowCell 0) 82 2 ≤ (911178368445792464445884953351 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_82) (by simpa only [blockSum_one] using cell_0_83) (by norm_num)

theorem sum_0_80_4 : blockSum (rowCell 0) 80 4 ≤ (938157784128573675949098515337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_80_2 sum_0_82_2 (by norm_num)

theorem sum_0_84_2 : blockSum (rowCell 0) 84 2 ≤ (428564167455125805984448306721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_84) (by simpa only [blockSum_one] using cell_0_85) (by norm_num)

theorem sum_0_86_2 : blockSum (rowCell 0) 86 2 ≤ (64275068369977761828741348809 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_86) (by simpa only [blockSum_one] using cell_0_87) (by norm_num)

theorem sum_0_84_4 : blockSum (rowCell 0) 84 4 ≤ (3321133379069947269656326947109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_84_2 sum_0_86_2 (by norm_num)

theorem sum_0_80_8 : blockSum (rowCell 0) 80 8 ≤ (7073764515584241973452721008457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_80_4 sum_0_84_4 (by norm_num)

theorem sum_0_88_2 : blockSum (rowCell 0) 88 2 ≤ (300205447187359658188358553411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_88) (by simpa only [blockSum_one] using cell_0_89) (by norm_num)

theorem sum_0_90_2 : blockSum (rowCell 0) 90 2 ≤ (1397423013846102646345022234747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_90) (by simpa only [blockSum_one] using cell_0_91) (by norm_num)

theorem sum_0_88_4 : blockSum (rowCell 0) 88 4 ≤ (1449225124891450468643407500901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_88_2 sum_0_90_2 (by norm_num)

theorem sum_0_92_2 : blockSum (rowCell 0) 92 2 ≤ (1296682015400714526980383686411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_92) (by simpa only [blockSum_one] using cell_0_93) (by norm_num)

theorem sum_0_94_2 : blockSum (rowCell 0) 94 2 ≤ (23986525881083617554836593413 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_94) (by simpa only [blockSum_one] using cell_0_95) (by norm_num)

theorem sum_0_92_4 : blockSum (rowCell 0) 92 4 ≤ (2496008309454895404722213357061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_92_2 sum_0_94_2 (by norm_num)

theorem sum_0_88_8 : blockSum (rowCell 0) 88 8 ≤ (5394458559237796342009028358863 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_88_4 sum_0_92_4 (by norm_num)

theorem sum_0_80_16 : blockSum (rowCell 0) 80 16 ≤ (311705576870550957886543734183 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_80_8 sum_0_88_8 (by norm_num)

theorem sum_0_64_32 : blockSum (rowCell 0) 64 32 ≤ (490904665739536090877911150427 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_64_16 sum_0_80_16 (by norm_num)

#print axioms sum_0_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
