import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_64_0 : expNegUpper (9384851939751866981 / 134953187093016000 : ℝ) ≤ (78675348322871625082900444011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_64_1 : expNegUpper (600627993041141791501 / 8637003973953024000 : ℝ) ≤ (15739681555237151563228045371 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_64 : rowCell 1 64 ≤ (22951671370454519215730988153 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (78675348322871625082900444011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15739681555237151563228045371 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_64_1
  · norm_num [gridPoint]

theorem exp_1_65_0 : expNegUpper (45426164136707899812167 / 653226219073131008000 : ℝ) ≤ (314793229018011428706927154121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_65_1 : expNegUpper (22713384638050861817703 / 326613109536565504000 : ℝ) ≤ (314501744123322553170743734163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (68867 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_65 : rowCell 1 65 ≤ (22944377411834252812884552197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (314793229018011428706927154121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (314501744123322553170743734163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_65_1
  · norm_num [gridPoint]

theorem exp_1_66_0 : expNegUpper (22903713604868919966807 / 329349989202770176000 : ℝ) ≤ (157250674535962993815933094059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (68867 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_66_1 : expNegUpper (9161766130405672727201 / 131739995681108070400 : ℝ) ≤ (39228997268111186939841548449 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215213 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_66 : rowCell 1 66 ≤ (45818630738873856389002291257 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (157250674535962993815933094059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39228997268111186939841548449 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_66_1
  · norm_num [gridPoint]

theorem exp_1_67_0 : expNegUpper (3079405901482495240147 / 44279771736246988800 : ℝ) ≤ (12553263617834268669395428751 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (215213 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_67_1 : expNegUpper (3849441133183683424453 / 55349714670308736000 : ℝ) ≤ (625582847854868463551833765051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_67 : rowCell 1 67 ≤ (91387826379429703937988556723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12553263617834268669395428751 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (625582847854868463551833765051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_67_1
  · norm_num [gridPoint]

theorem exp_1_68_0 : expNegUpper (11644289516636328136751 / 167429002996906112000 : ℝ) ≤ (156395521934956477135743097283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_68_1 : expNegUpper (46580168106967882736763 / 669716011987624448000 : ℝ) ≤ (124555343291150531751983967079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_68 : rowCell 1 68 ≤ (18206289114860946718569192441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (156395521934956477135743097283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124555343291150531751983967079 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_68_1
  · norm_num [gridPoint]

theorem exp_1_69_0 : expNegUpper (1878625833400005539883 / 27010331449491968000 : ℝ) ≤ (24911038885849129301163430967 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721809 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_69_1 : expNegUpper (939389283413161105901 / 13505165724745984000 : ℝ) ≤ (77408042798507357829274372399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344377 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_69 : rowCell 1 69 ≤ (5660668476964706523616780831 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24911038885849129301163430967 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77408042798507357829274372399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_69_1
  · norm_num [gridPoint]

theorem exp_1_70_0 : expNegUpper (607135407947955810019 / 8728505112727296000 : ℝ) ≤ (619263614350983838014756295493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344377 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_70_1 : expNegUpper (1214389532861881166599 / 17457010225454592000 : ℝ) ≤ (615066579207116064848515588457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_70 : rowCell 1 70 ≤ (90008466682789919772171264499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (619263614350983838014756295493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (615066579207116064848515588457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_70_1
  · norm_num [gridPoint]

theorem exp_1_71_0 : expNegUpper (47749916013705203329289 / 686411349653914112000 : ℝ) ≤ (61506586785435368655343372771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1721977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_71_1 : expNegUpper (1193884023304311501819 / 17160283741347852800 : ℝ) ≤ (610206193335558530809202937023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430521 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_71 : rowCell 1 71 ≤ (89347939532335874201841252337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61506586785435368655343372771 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (610206193335558530809202937023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_71_1
  · norm_num [gridPoint]

theorem exp_1_72_0 : expNegUpper (1203642960215818391739 / 17300553470521356800 : ℝ) ≤ (122041099804928577640092232193 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (430521 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_72_1 : expNegUpper (48151981614673985750311 / 692022138820854272000 : ℝ) ≤ (302353849112781371007002466739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344441 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_72 : rowCell 1 72 ≤ (88592561867060649036859763417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (122041099804928577640092232193 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (302353849112781371007002466739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_72_1
  · norm_num [gridPoint]

theorem exp_1_73_0 : expNegUpper (16181326332353932310453 / 232551922097849856000 : ℝ) ≤ (75588377657582942754721066473 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344441 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_73_1 : expNegUpper (8091843970242764876513 / 116275961048924928000 : ℝ) ≤ (299298592238491194811777652121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861171 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_73 : rowCell 1 73 ≤ (43873011888005741876505230547 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75588377657582942754721066473 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (299298592238491194811777652121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_73_1
  · norm_num [gridPoint]

theorem exp_1_74_0 : expNegUpper (1566230648682593083 / 22505991426304000 : ℝ) ≤ (598596525110077860620509270967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861171 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_74_1 : expNegUpper (3132967522870970709 / 45011982852608000 : ℝ) ≤ (1156058881400541374808762309 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722493 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_74 : rowCell 1 74 ≤ (43406116389561159340598991233 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (598596525110077860620509270967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1156058881400541374808762309 / 1953125000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_74_1
  · norm_num [gridPoint]

theorem exp_1_75_0 : expNegUpper (49347914723779093135797 / 708991536156205568000 : ℝ) ≤ (591901505709316908247141293693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722493 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_75_1 : expNegUpper (12339163194304904171629 / 177247884039051392000 : ℝ) ≤ (584651312481169689234574696011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_75 : rowCell 1 75 ≤ (85795288561622875703669154949 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (591901505709316908247141293693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (584651312481169689234574696011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_75_1
  · norm_num [gridPoint]

theorem exp_1_76_0 : expNegUpper (4146134153895385128047 / 59557806545513856000 : ℝ) ≤ (584650688864408909891650954749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722659 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_76_1 : expNegUpper (3317545300725155604221 / 47646245236411084800 : ℝ) ≤ (28843723129878027495236468531 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722839 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_76 : rowCell 1 76 ≤ (84699457602360079621538589137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (584650688864408909891650954749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28843723129878027495236468531 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_76_1
  · norm_num [gridPoint]

theorem exp_1_77_0 : expNegUpper (10032360626513253155023 / 144083731848376422400 : ℝ) ≤ (576873857036047412481575765859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43071 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_77_1 : expNegUpper (25086103869085358093793 / 360209329620941056000 : ℝ) ≤ (568602263875570776675017369249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_77 : rowCell 1 77 ≤ (83529147875577579885265591789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (576873857036047412481575765859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (568602263875570776675017369249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_77_1
  · norm_num [gridPoint]

theorem exp_1_78_0 : expNegUpper (25286252286791336290257 / 363083239121676544000 : ℝ) ≤ (1421504191069420107319387777 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_78_1 : expNegUpper (50583747451438409788393 / 726166478243353088000 : ℝ) ≤ (69983261952982643633857709041 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861621 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_78 : rowCell 1 78 ≤ (82288883795768753316141322083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1421504191069420107319387777 / 2500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (69983261952982643633857709041 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_78_1
  · norm_num [gridPoint]

theorem exp_1_79_0 : expNegUpper (679809655495099849091 / 9759161807341056000 : ℝ) ≤ (279932763152192068885488025247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (861621 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_79_1 : expNegUpper (42498173869182551329 / 609947612958816000 : ℝ) ≤ (275348941404202119809294662673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344693 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_79 : rowCell 1 79 ≤ (19771308975663428527845439 / 244140625000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (279932763152192068885488025247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (275348941404202119809294662673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_79_1
  · norm_num [gridPoint]

theorem exp_1_80_0 : expNegUpper (3212591993159647550507 / 46108164447722528000 : ℝ) ≤ (137674332897514275858207291717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (344693 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_80_1 : expNegUpper (51414401305251318335871 / 737730631163560448000 : ℝ) ≤ (270564966448420008000087539073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_80 : rowCell 1 80 ≤ (79617025064942475395685410137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (137674332897514275858207291717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (270564966448420008000087539073 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_80_1
  · norm_num [gridPoint]

theorem exp_1_81_0 : expNegUpper (1671605088747965667369 / 23985385970396672000 : ℝ) ≤ (541129399712732935363030788619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723701 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_81_1 : expNegUpper (167204953001528473357 / 2398538597039667200 : ℝ) ≤ (531194777829588625753407514341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34479 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_81 : rowCell 1 81 ≤ (39097421221319674458069123301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (541129399712732935363030788619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (531194777829588625753407514341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_81_1
  · norm_num [gridPoint]

theorem exp_1_82_0 : expNegUpper (1741353057878962001729 / 24979537910226278400 : ℝ) ≤ (26559713128765953963654751127 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (34479 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_82_1 : expNegUpper (17418407003675077846087 / 249795379102262784000 : ℝ) ≤ (104185004381828023883489206157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_82 : rowCell 1 82 ≤ (38360741744013209387412788571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26559713128765953963654751127 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (104185004381828023883489206157 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_82_1
  · norm_num [gridPoint]

theorem exp_1_83_0 : expNegUpper (4051075679879906202113 / 58096011372079616000 : ℝ) ≤ (520924524445022061782808380377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_83_1 : expNegUpper (1013066693062388181879 / 14524002843019904000 : ℝ) ≤ (255176598154227660058607061991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_83 : rowCell 1 83 ≤ (3760084896796040507024247091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (520924524445022061782808380377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (255176598154227660058607061991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_83_1
  · norm_num [gridPoint]

theorem exp_1_84_0 : expNegUpper (530899440497353441443 / 7611329966730368000 : ℝ) ≤ (510352716461780849543756620601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724489 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_84_1 : expNegUpper (2124251460298773169123 / 30445319866921472000 : ℝ) ≤ (249755810404199529545109933983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_84 : rowCell 1 84 ≤ (14728042954746407022970245777 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (510352716461780849543756620601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (249755810404199529545109933983 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_84_1
  · norm_num [gridPoint]

theorem exp_1_85_0 : expNegUpper (17839494120865732443809 / 255680227938264576000 : ℝ) ≤ (499511158375717974120819293823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724779 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_85_1 : expNegUpper (8922614401339885263071 / 127840113969132288000 : ℝ) ≤ (97686454656704563513479776837 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_85 : rowCell 1 85 ≤ (18010430660504679969763412981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (499511158375717974120819293823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (97686454656704563513479776837 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_85_1
  · norm_num [gridPoint]

theorem exp_1_86_0 : expNegUpper (26974804384681493458957 / 386485604631152896000 : ℝ) ≤ (122107957008231583748301227831 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725081 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_86_1 : expNegUpper (2158707109331711169513 / 30918848370492231680 : ℝ) ≤ (477146667366180750638701653391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431349 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_86 : rowCell 1 86 ≤ (17602712849108087204887718529 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (122107957008231583748301227831 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (477146667366180750638701653391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_86_1
  · norm_num [gridPoint]

theorem exp_1_87_0 : expNegUpper (2175333330494854385313 / 31156982920622919680 : ℝ) ≤ (29821639939973535650180001773 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431349 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_87_1 : expNegUpper (6800283809446047366917 / 97365571626946624000 : ℝ) ≤ (465685738631685020916595742177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431431 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_87 : rowCell 1 87 ≤ (1718803872184833356577553107 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29821639939973535650180001773 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (465685738631685020916595742177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_87_1
  · norm_num [gridPoint]

theorem exp_1_88_0 : expNegUpper (2284152743081706758551 / 32704198961441472000 : ℝ) ≤ (116421331736762967169749628391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431431 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_88_1 : expNegUpper (18279824875734919133341 / 261633591691531776000 : ℝ) ≤ (454079739562685790487308482581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (107879 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_88 : rowCell 1 88 ≤ (16767523750329253112208815847 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (116421331736762967169749628391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (454079739562685790487308482581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_88_1
  · norm_num [gridPoint]

theorem exp_1_89_0 : expNegUpper (2210344659058817654567 / 31635992617574912000 : ℝ) ≤ (113519836054074133325566307169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (107879 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_89_1 : expNegUpper (1105586003610811227219 / 15817996308787456000 : ℝ) ≤ (110589535867454345767912290403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_89 : rowCell 1 89 ≤ (65369026995126769774957579529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113519836054074133325566307169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (110589535867454345767912290403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_89_1
  · norm_num [gridPoint]

theorem exp_1_90_0 : expNegUpper (27850097591119221919371 / 398460847054952704000 : ℝ) ≤ (442357764138420788330920440753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1726417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_90_1 : expNegUpper (55721757127914437547181 / 796921694109905408000 : ℝ) ≤ (215274778734210315323165407049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (863391 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_90 : rowCell 1 90 ≤ (31826593072121316209204261939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (442357764138420788330920440753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (215274778734210315323165407049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_90_1
  · norm_num [gridPoint]

theorem exp_1_91_0 : expNegUpper (18714803981201205452663 / 267655470362064384000 : ℝ) ≤ (215274596905686406900887480421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (863391 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_91_1 : expNegUpper (936114257694417211463 / 13382773518103219200 : ℝ) ≤ (26167602783642799753876255047 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_91 : rowCell 1 91 ≤ (61926675713288362681776796437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (215274596905686406900887480421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26167602783642799753876255047 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_91_1
  · norm_num [gridPoint]

theorem exp_1_92_0 : expNegUpper (2829563837645230282549 / 40451698318411801600 : ℝ) ≤ (41868129619962237020421901851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_92_1 : expNegUpper (56614605174130993511811 / 809033966368236032000 : ℝ) ≤ (406781054625221815571410660799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431887 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_92 : rowCell 1 92 ≤ (7524182031059807152838384251 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41868129619962237020421901851 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (406781054625221815571410660799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_92_1
  · norm_num [gridPoint]

theorem exp_1_93_0 : expNegUpper (57040799602480058446779 / 815124359956034048000 : ℝ) ≤ (203390360617834854027403013529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (431887 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_93_1 : expNegUpper (28532508128825483374169 / 407562179978017024000 : ℝ) ≤ (9871834117004577762331089079 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_93 : rowCell 1 93 ≤ (58457336181076802552540440383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (203390360617834854027403013529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9871834117004577762331089079 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_93_1
  · norm_num [gridPoint]

theorem exp_1_94_0 : expNegUpper (383286603231124143163 / 5474917278997248000 : ℝ) ≤ (394873045859090941641513045121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1727949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_94_1 : expNegUpper (766907982727514655019 / 10949834557994496000 : ℝ) ≤ (191491513736885707937385510091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864181 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_94 : rowCell 1 94 ≤ (56721963722498208103611765079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (394873045859090941641513045121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (191491513736885707937385510091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_94_1
  · norm_num [gridPoint]

theorem exp_1_95_0 : expNegUpper (57947859391808941463057 / 827373662048895488000 : ℝ) ≤ (382982722830973236366981638799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864181 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_95_1 : expNegUpper (1811683203350235542973 / 25855426939027984000 : ℝ) ≤ (185566664485765903552725806329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (864393 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_95 : rowCell 1 95 ≤ (54990820023578959083134827461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (382982722830973236366981638799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (185566664485765903552725806329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_95_1
  · norm_num [gridPoint]

theorem sum_1_64_2 : blockSum (rowCell 1) 64 2 ≤ (917920975645775440572310807 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_64) (by simpa only [blockSum_one] using cell_1_65) (by norm_num)

theorem sum_1_66_2 : blockSum (rowCell 1) 66 2 ≤ (183025087857177416715993139237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_66) (by simpa only [blockSum_one] using cell_1_67) (by norm_num)

theorem sum_1_64_4 : blockSum (rowCell 1) 64 4 ≤ (366609282986332504830455300637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_64_2 sum_1_66_2 (by norm_num)

theorem sum_1_68_2 : blockSum (rowCell 1) 68 2 ≤ (181602141205740037970714455501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_68) (by simpa only [blockSum_one] using cell_1_69) (by norm_num)

theorem sum_1_70_2 : blockSum (rowCell 1) 70 2 ≤ (44839101553781448493503129209 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_70) (by simpa only [blockSum_one] using cell_1_71) (by norm_num)

theorem sum_1_68_4 : blockSum (rowCell 1) 68 4 ≤ (360958547420865831944726972337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_68_2 sum_1_70_2 (by norm_num)

theorem sum_1_64_8 : blockSum (rowCell 1) 64 8 ≤ (363783915203599168387591136487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_64_4 sum_1_68_4 (by norm_num)

theorem sum_1_72_2 : blockSum (rowCell 1) 72 2 ≤ (176338585643072132789870224511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_72) (by simpa only [blockSum_one] using cell_1_73) (by norm_num)

theorem sum_1_74_2 : blockSum (rowCell 1) 74 2 ≤ (34521504268149038876973427483 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_74) (by simpa only [blockSum_one] using cell_1_75) (by norm_num)

theorem sum_1_72_4 : blockSum (rowCell 1) 72 4 ≤ (174473053491908663587368680963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_72_2 sum_1_74_2 (by norm_num)

theorem sum_1_76_2 : blockSum (rowCell 1) 76 2 ≤ (84114302738968829753402090463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_76) (by simpa only [blockSum_one] using cell_1_77) (by norm_num)

theorem sum_1_78_2 : blockSum (rowCell 1) 78 2 ≤ (163272165360086156566196240227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_78) (by simpa only [blockSum_one] using cell_1_79) (by norm_num)

theorem sum_1_76_4 : blockSum (rowCell 1) 76 4 ≤ (331500770838023816073000421153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_76_2 sum_1_78_2 (by norm_num)

theorem sum_1_72_8 : blockSum (rowCell 1) 72 8 ≤ (680446877821841143247737783079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_72_4 sum_1_76_4 (by norm_num)

theorem sum_1_64_16 : blockSum (rowCell 1) 64 16 ≤ (1408014708229039480022920056053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_64_8 sum_1_72_8 (by norm_num)

theorem sum_1_80_2 : blockSum (rowCell 1) 80 2 ≤ (157811867507581824311823656739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_80) (by simpa only [blockSum_one] using cell_1_81) (by norm_num)

theorem sum_1_82_2 : blockSum (rowCell 1) 82 2 ≤ (75961590711973614457655259481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_82) (by simpa only [blockSum_one] using cell_1_83) (by norm_num)

theorem sum_1_80_4 : blockSum (rowCell 1) 80 4 ≤ (309735048931529053227134175701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_80_2 sum_1_82_2 (by norm_num)

theorem sum_1_84_2 : blockSum (rowCell 1) 84 2 ≤ (145681937415750754993904880809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_84) (by simpa only [blockSum_one] using cell_1_85) (by norm_num)

theorem sum_1_86_2 : blockSum (rowCell 1) 86 2 ≤ (34790751570956420770663249599 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_86) (by simpa only [blockSum_one] using cell_1_87) (by norm_num)

theorem sum_1_84_4 : blockSum (rowCell 1) 84 4 ≤ (56968988739915287615311575841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_84_2 sum_1_86_2 (by norm_num)

theorem sum_1_80_8 : blockSum (rowCell 1) 80 8 ≤ (297289996315552745651846027453 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_80_4 sum_1_84_4 (by norm_num)

theorem sum_1_88_2 : blockSum (rowCell 1) 88 2 ≤ (132439121996443782223792842917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_88) (by simpa only [blockSum_one] using cell_1_89) (by norm_num)

theorem sum_1_90_2 : blockSum (rowCell 1) 90 2 ≤ (25115972371506199020037064063 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_90) (by simpa only [blockSum_one] using cell_1_91) (by norm_num)

theorem sum_1_88_4 : blockSum (rowCell 1) 88 4 ≤ (8063093245436711791374317601 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_88_2 sum_1_90_2 (by norm_num)

theorem sum_1_92_2 : blockSum (rowCell 1) 92 2 ≤ (118650792429555259775247514391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_92) (by simpa only [blockSum_one] using cell_1_93) (by norm_num)

theorem sum_1_94_2 : blockSum (rowCell 1) 94 2 ≤ (5585639187303858359337329627 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_94) (by simpa only [blockSum_one] using cell_1_95) (by norm_num)

theorem sum_1_92_4 : blockSum (rowCell 1) 92 4 ≤ (230363576175632426961994106931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_92_2 sum_1_94_2 (by norm_num)

theorem sum_1_88_8 : blockSum (rowCell 1) 88 8 ≤ (488382560029607204285972270163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_88_4 sum_1_92_4 (by norm_num)

theorem sum_1_80_16 : blockSum (rowCell 1) 80 16 ≤ (1082962552660712695589664325069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_80_8 sum_1_88_8 (by norm_num)

theorem sum_1_64_32 : blockSum (rowCell 1) 64 32 ≤ (1245488630444876087806292190561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_64_16 sum_1_80_16 (by norm_num)

#print axioms sum_1_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
