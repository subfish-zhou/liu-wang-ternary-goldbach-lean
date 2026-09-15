import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_0_1 : expNegUpper (24000813532832648690191 / 346420028311290368000 : ℝ) ≤ (815580532568634833155407387469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (343637 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_0 : rowCell 0 0 ≤ (112942957014765308223963697477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (733261561190919419785343723617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (815580532568634833155407387469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact pilot_exp_upper
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_0_1
  · norm_num [gridPoint]

theorem exp_0_1_0 : expNegUpper (2697466796094629792271 / 38934366418846208000 : ℝ) ≤ (815577180543154427588644983493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (343637 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_1_1 : expNegUpper (269343607495983998211 / 3893436641884620800 : ℝ) ≤ (904536003409464779215663357303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (429199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_1 : rowCell 0 1 ≤ (125432198788013699991488777457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (815577180543154427588644983493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (904536003409464779215663357303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_1_1
  · norm_num [gridPoint]

theorem exp_0_2_0 : expNegUpper (2451847924188916968779 / 35442140553369651200 : ℝ) ≤ (90453236970679739215376787931 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (429199 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_2_1 : expNegUpper (24482787884681631055461 / 354421405533696512000 : ℝ) ≤ (62522877774211266515072349553 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (857723 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_2 : rowCell 0 2 ≤ (69453451893958173721028066373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90453236970679739215376787931 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62522877774211266515072349553 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_2_1
  · norm_num [gridPoint]

theorem exp_0_3_0 : expNegUpper (24761516048722929132189 / 358456351603532288000 : ℝ) ≤ (1000362115931930459110009804893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (857723 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_3_1 : expNegUpper (6181603288825127267167 / 89614087900883072000 : ℝ) ≤ (137910335523040923596345736963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (857067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_3 : rowCell 0 3 ≤ (2396869825278947292466818273 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1000362115931930459110009804893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137910335523040923596345736963 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_3_1
  · norm_num [gridPoint]

theorem exp_0_4_0 : expNegUpper (27784801752990659103 / 402793484421248000 : ℝ) ≤ (8619362877296743820421204409 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (857067 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_4_1 : expNegUpper (110985824350372624923 / 1611173937684992000 : ℝ) ≤ (606735879579836163376675456519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (85643 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_4 : rowCell 0 4 ≤ (84469753291392535405897192673 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8619362877296743820421204409 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (606735879579836163376675456519 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_4_1
  · norm_num [gridPoint]

theorem exp_0_5_0 : expNegUpper (25252905821133808598387 / 366594758660469248000 : ℝ) ≤ (606733601821566911423615144627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (85643 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_5_1 : expNegUpper (12609494923810136200773 / 183297379330234624000 : ℝ) ≤ (266217951363806904068739623991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (855811 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_5 : rowCell 0 5 ≤ (231939224602869351018566669 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (606733601821566911423615144627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (266217951363806904068739623991 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_5_1
  · norm_num [gridPoint]

theorem exp_0_6_0 : expNegUpper (12750639385694111039157 / 185349109823785216000 : ℝ) ≤ (1331084870073109350821507042673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (855811 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_6_1 : expNegUpper (5093592250799690235869 / 74139643929514086400 : ℝ) ≤ (1456260777737400081307530900589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1710421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_6 : rowCell 0 6 ≤ (25406968611774725318177171907 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1331084870073109350821507042673 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1456260777737400081307530900589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_6_1
  · norm_num [gridPoint]

theorem exp_0_7_0 : expNegUpper (572254453795410674701 / 8329433754231705600 : ℝ) ≤ (728127774421643545122130782611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1710421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_7_1 : expNegUpper (357204648476486439863 / 5205896096394816000 : ℝ) ≤ (1589073656682180914450902638569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (341851 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_7 : rowCell 0 7 ≤ (222068141704875216190031842053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (728127774421643545122130782611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1589073656682180914450902638569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_7_1
  · norm_num [gridPoint]

theorem exp_0_8_0 : expNegUpper (3250428845211028772143 / 47371707067379776000 : ℝ) ≤ (794534037749877781462396660601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (341851 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_8_1 : expNegUpper (25971320148884636602983 / 378973656539038208000 : ℝ) ≤ (1729579282851559666646978880957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (427031 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_8 : rowCell 0 8 ≤ (241998746968213925300150197371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (794534037749877781462396660601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1729579282851559666646978880957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_8_1
  · norm_num [gridPoint]

theorem exp_0_9_0 : expNegUpper (1050289191456444730167 / 15325825297736192000 : ℝ) ≤ (216196667513835231947939278067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (427031 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_9_1 : expNegUpper (524514552441398734139 / 7662912648868096000 : ℝ) ≤ (1877788157676201653544168250753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1707027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_9 : rowCell 0 9 ≤ (263052041407465213388743338001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (216196667513835231947939278067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1877788157676201653544168250753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_9_1
  · norm_num [gridPoint]

theorem exp_0_10_0 : expNegUpper (1472936527072266184539 / 21518913702973696000 : ℝ) ≤ (375556369012817341175639140443 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1707027 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_10_1 : expNegUpper (2942440789133507856789 / 43037827405947392000 : ℝ) ≤ (508417056636430205570290428661 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426491 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_10 : rowCell 0 10 ≤ (285226453415210876889831423511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (375556369012817341175639140443 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (508417056636430205570290428661 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_10_1
  · norm_num [gridPoint]

theorem exp_0_11_0 : expNegUpper (26770323856695896108789 / 391558099169403392000 : ℝ) ≤ (2033661536789447839408888886153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (426491 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_11_1 : expNegUpper (53480097163236370689 / 783116198338806784 : ℝ) ≤ (2197143018144582939485933477903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (852467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_11 : rowCell 0 11 ≤ (38564258657407105992536045013 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2033661536789447839408888886153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2197143018144582939485933477903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_11_1
  · norm_num [gridPoint]

theorem exp_0_12_0 : expNegUpper (54059277773870158689 / 791597179982070784 : ℝ) ≤ (2197135945087860828266390182111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (852467 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_12_1 : expNegUpper (26999982052658427336211 / 395798589991035392000 : ℝ) ≤ (1184045060928031500177323363501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26624 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_12 : rowCell 0 12 ≤ (166450193185922722757305394063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2197135945087860828266390182111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1184045060928031500177323363501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_12_1
  · norm_num [gridPoint]

theorem exp_0_13_0 : expNegUpper (3032312507817443084211 / 44451324346491392000 : ℝ) ≤ (1184041330264716194229819303129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26624 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_13_1 : expNegUpper (1514543194870052411961 / 22225662173245696000 : ℝ) ≤ (2546340029968365857988113099069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (170297 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_13 : rowCell 0 13 ≤ (71672823578547088449316419451 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1184041330264716194229819303129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2546340029968365857988113099069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_13_1
  · norm_num [gridPoint]

theorem exp_0_14_0 : expNegUpper (551077097986005361561 / 8086961731031296000 : ℝ) ≤ (254633217665208389182141783793 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (170297 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_14_1 : expNegUpper (1101017797558575212433 / 16173923462062592000 : ℝ) ≤ (2731675367254099541047186755277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (425509 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_14 : rowCell 0 14 ≤ (48109631507692703017057076853 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (254633217665208389182141783793 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2731675367254099541047186755277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_14_1
  · norm_num [gridPoint]

theorem exp_0_15_0 : expNegUpper (27818775866103567034017 / 408657092290462208000 : ℝ) ≤ (170729194970814564922237854607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (425509 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_15_1 : expNegUpper (1736937146181711546991 / 25541068268153888000 : ℝ) ≤ (1461915262980378225780146819997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (425283 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_15 : rowCell 0 15 ≤ (206201984710286501480172583913 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170729194970814564922237854607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1461915262980378225780146819997 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_15_1
  · norm_num [gridPoint]

theorem exp_0_16_0 : expNegUpper (195038787938232856631 / 2867978724549408000 : ℝ) ≤ (23390575062165566156947711609 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (425283 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_16_1 : expNegUpper (623520793329524521499 / 9177531918558105600 : ℝ) ≤ (3122491719419786611621742830313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1700259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_16 : rowCell 0 16 ≤ (440902620106606943251550274001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23390575062165566156947711609 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3122491719419786611621742830313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_16_1
  · norm_num [gridPoint]

theorem exp_0_17_0 : expNegUpper (5670858736528961553931 / 83468723737104486400 : ℝ) ≤ (24394395945974113046874403983 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1700259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_17_1 : expNegUpper (14163889507033341593343 / 208671809342761216000 : ℝ) ≤ (3327297462434011183615207557727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (339883 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_17 : rowCell 0 17 ≤ (752518020463569800770461667 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24394395945974113046874403983 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3327297462434011183615207557727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_17_1
  · norm_num [gridPoint]

theorem exp_0_18_0 : expNegUpper (14312455258530021503727 / 210860569670842624000 : ℝ) ≤ (3327288030693764091303056449387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (339883 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_18_1 : expNegUpper (28599034273960270638613 / 421721139341685248000 : ℝ) ≤ (707567896283868165640860788117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (8493 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_18 : rowCell 0 18 ≤ (500611266071286774848177839531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3327288030693764091303056449387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (707567896283868165640860788117 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_18_1
  · norm_num [gridPoint]

theorem exp_0_19_0 : expNegUpper (4143003004830090867 / 61092687928832000 : ℝ) ≤ (3537829659447792114324761501269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1698601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_19_1 : expNegUpper (1034846289313548837 / 15273171982208000 : ℝ) ≤ (3753664052040225971412810252213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (339563 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_19 : rowCell 0 19 ≤ (265851136196543846914116318557 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3537829659447792114324761501269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3753664052040225971412810252213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_19_1
  · norm_num [gridPoint]

theorem exp_0_20_0 : expNegUpper (7292977499968244217083 / 107636173892819072000 : ℝ) ≤ (938413461113311297645918916967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (339563 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_20_1 : expNegUpper (29147320600068555656811 / 430544695571276288000 : ℝ) ≤ (397427375687189587229963400187 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (848529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_20 : rowCell 0 20 ≤ (563527423748583601861874625341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (938413461113311297645918916967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (397427375687189587229963400187 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_20_1
  · norm_num [gridPoint]

theorem exp_0_21_0 : expNegUpper (29448312632947968949539 / 434990731144704512000 : ℝ) ≤ (397426316972542595535626049567 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (848529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_21_1 : expNegUpper (2942437165096054668121 / 43499073114470451200 : ℝ) ≤ (4199129650527296045704847068031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (212041 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_21 : rowCell 0 21 ≤ (149002786933860108530574697971 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (397426316972542595535626049567 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4199129650527296045704847068031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_21_1
  · norm_num [gridPoint]

theorem exp_0_22_0 : expNegUpper (330296265002816741889 / 4882884500265420800 : ℝ) ≤ (2099559345652703740502735811821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (212041 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_22_1 : expNegUpper (3300374957429181372729 / 48828845002654208000 : ℝ) ≤ (4427653814780396787105304971581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_22 : rowCell 0 22 ≤ (6290720017597002836954099601 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2099559345652703740502735811821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4427653814780396787105304971581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_22_1
  · norm_num [gridPoint]

theorem exp_0_23_0 : expNegUpper (30006973644128237058809 / 443951317208826368000 : ℝ) ≤ (553455311546684734410384647993 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_23_1 : expNegUpper (3748042436264182425741 / 55493914651103296000 : ℝ) ≤ (4659232281573157778272975495479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1694951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_23 : rowCell 0 23 ≤ (13252461450104867790755547063 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (553455311546684734410384647993 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4659232281573157778272975495479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_23_1
  · norm_num [gridPoint]

theorem exp_0_24_0 : expNegUpper (6057850401382161309 / 89693173539904000 : ℝ) ≤ (1164805151561618054750381723183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1694951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_24_1 : expNegUpper (48427642020882679303 / 717545388319232000 : ℝ) ≤ (38228267949045700903415986717 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_24 : rowCell 0 24 ≤ (696572427128905120294347493221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1164805151561618054750381723183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38228267949045700903415986717 / 7812500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_24_1
  · norm_num [gridPoint]

theorem exp_0_25_0 : expNegUpper (3397056547882206884183 / 50333695166218752000 : ℝ) ≤ (1223301570207697044135489373381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (847151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_25_1 : expNegUpper (1697344162667551364387 / 25166847583109376000 : ℝ) ≤ (1025787179851911496395338080621 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1693679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_25 : rowCell 0 25 ≤ (73082361204055293033910737997 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1223301570207697044135489373381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1025787179851911496395338080621 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_25_1
  · norm_num [gridPoint]

theorem exp_0_26_0 : expNegUpper (15429877204277025012907 / 228781741799086336000 : ℝ) ≤ (5128923554175999205957028406427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1693679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_26_1 : expNegUpper (6167821095468971223753 / 91512696719634534400 : ℝ) ≤ (5365683766697490165377914497893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (846541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_26 : rowCell 0 26 ≤ (765276194586859692233351095321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5128923554175999205957028406427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5365683766697490165377914497893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_26_1
  · norm_num [gridPoint]

theorem exp_0_27_0 : expNegUpper (6229599686418403495713 / 92429309801226342400 : ℝ) ≤ (167677222102742908354532135937 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (846541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_27_1 : expNegUpper (7782004475844278993209 / 115536637251532928000 : ℝ) ≤ (5602739315821547197770733574143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1692511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_27 : rowCell 0 27 ≤ (15996526849687422920243340989 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (167677222102742908354532135937 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5602739315821547197770733574143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_27_1
  · norm_num [gridPoint]

theorem exp_0_28_0 : expNegUpper (873284749830344751249 / 12965345908884608000 : ℝ) ≤ (2801363178678309702823668694641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1692511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_28_1 : expNegUpper (3490993577605705650027 / 51861383635538432000 : ℝ) ≤ (1167872598647333960481034587989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_28 : rowCell 0 28 ≤ (166873487089482714541892382577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2801363178678309702823668694641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1167872598647333960481034587989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_28_1
  · norm_num [gridPoint]

theorem exp_0_29_0 : expNegUpper (1269220883451755098163 / 18855247789572608000 : ℝ) ≤ (1459837438018765371236144756779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_29_1 : expNegUpper (634237767098124149601 / 9427623894786304000 : ℝ) ≤ (6074802730266673035411584810349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_29 : rowCell 0 29 ≤ (868790703133730135126479599519 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1459837438018765371236144756779 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6074802730266673035411584810349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_29_1
  · norm_num [gridPoint]

theorem exp_0_30_0 : expNegUpper (16012410850817531717481 / 238016387532269824000 : ℝ) ≤ (6074789223774984064527399572507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1691441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_30_1 : expNegUpper (32006866365080332591321 / 476032775064539648000 : ℝ) ≤ (1577074628566710149392566608269 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1690943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_30 : rowCell 0 30 ≤ (902985883288399501312006658499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6074789223774984064527399572507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1577074628566710149392566608269 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_30_1
  · norm_num [gridPoint]

theorem exp_0_31_0 : expNegUpper (3591239981361623968521 / 53411910410613248000 : ℝ) ≤ (1261656952146897341831190511903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1690943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_31_1 : expNegUpper (22433254320355814523 / 333824440066332800 : ℝ) ≤ (6539087033636506148802671585303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422617 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_31 : rowCell 0 31 ≤ (468420946903064652195619347421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1261656952146897341831190511903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6539087033636506148802671585303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_31_1
  · norm_num [gridPoint]

theorem sum_0_0_2 : blockSum (rowCell 0) 0 2 ≤ (119187577901389504107726237467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_0) (by simpa only [blockSum_one] using cell_0_1) (by norm_num)

theorem sum_0_2_2 : blockSum (rowCell 0) 2 2 ≤ (146153286302884487079966251109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_2) (by simpa only [blockSum_one] using cell_0_3) (by norm_num)

theorem sum_0_0_4 : blockSum (rowCell 0) 0 4 ≤ (2072975501595890556153847567 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_0_2 sum_0_2_2 (by norm_num)

theorem sum_0_4_2 : blockSum (rowCell 0) 4 2 ≤ (177245443132540275813323860273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_4) (by simpa only [blockSum_one] using cell_0_5) (by norm_num)

theorem sum_0_6_2 : blockSum (rowCell 0) 6 2 ≤ (425323890599073018735449217309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_6) (by simpa only [blockSum_one] using cell_0_7) (by norm_num)

theorem sum_0_4_4 : blockSum (rowCell 0) 4 4 ≤ (155962955372830714072419387571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_4_2 sum_0_6_2 (by norm_num)

theorem sum_0_0_8 : blockSum (rowCell 0) 0 8 ≤ (1310496505272701552737481915007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_0_4 sum_0_4_4 (by norm_num)

theorem sum_0_8_2 : blockSum (rowCell 0) 8 2 ≤ (126262697093919784672223383843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_8) (by simpa only [blockSum_one] using cell_0_9) (by norm_num)

theorem sum_0_10_2 : blockSum (rowCell 0) 10 2 ≤ (118748104534893544966023956723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_10) (by simpa only [blockSum_one] using cell_0_11) (by norm_num)

theorem sum_0_8_4 : blockSum (rowCell 0) 8 4 ≤ (1098791311050146863519013318987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_8_2 sum_0_10_2 (by norm_num)

theorem sum_0_12_2 : blockSum (rowCell 0) 12 2 ≤ (691264504264580887761192885381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_12) (by simpa only [blockSum_one] using cell_0_13) (by norm_num)

theorem sum_0_14_2 : blockSum (rowCell 0) 14 2 ≤ (15945620429642292541936035653 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_14) (by simpa only [blockSum_one] using cell_0_15) (by norm_num)

theorem sum_0_12_4 : blockSum (rowCell 0) 12 4 ≤ (1488545525746695514857994668031 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_12_2 sum_0_14_2 (by norm_num)

theorem sum_0_8_8 : blockSum (rowCell 0) 8 8 ≤ (1293668418398421189188503993509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_8_4 sum_0_12_4 (by norm_num)

theorem sum_0_0_16 : blockSum (rowCell 0) 0 16 ≤ (155913333682781757244579596081 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_0_8 sum_0_8_8 (by norm_num)

theorem sum_0_16_2 : blockSum (rowCell 0) 16 2 ≤ (227806595724084517183272203969 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_16) (by simpa only [blockSum_one] using cell_0_17) (by norm_num)

theorem sum_0_18_2 : blockSum (rowCell 0) 18 2 ≤ (206462707692874893735282095329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_18) (by simpa only [blockSum_one] using cell_0_19) (by norm_num)

theorem sum_0_16_4 : blockSum (rowCell 0) 16 4 ≤ (1943539921360712537409499292521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_16_2 sum_0_18_2 (by norm_num)

theorem sum_0_20_2 : blockSum (rowCell 0) 20 2 ≤ (46381542859360961439366936689 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_20) (by simpa only [blockSum_one] using cell_0_21) (by norm_num)

theorem sum_0_22_2 : blockSum (rowCell 0) 22 2 ≤ (5166780297059774692932749253 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_22) (by simpa only [blockSum_one] using cell_0_23) (by norm_num)

theorem sum_0_20_4 : blockSum (rowCell 0) 20 4 ≤ (98049345829958708368694429219 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_20_2 sum_0_22_2 (by norm_num)

theorem sum_0_16_8 : blockSum (rowCell 0) 16 8 ≤ (1098693391777420061656715005749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_16_4 sum_0_20_4 (by norm_num)

theorem sum_0_24_2 : blockSum (rowCell 0) 24 2 ≤ (1427396039169458050633454873191 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_24) (by simpa only [blockSum_one] using cell_0_25) (by norm_num)

theorem sum_0_26_2 : blockSum (rowCell 0) 26 2 ≤ (1565102537071230838245518144771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_26) (by simpa only [blockSum_one] using cell_0_27) (by norm_num)

theorem sum_0_24_4 : blockSum (rowCell 0) 24 4 ≤ (1496249288120344444439486508981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_24_2 sum_0_26_2 (by norm_num)

theorem sum_0_28_2 : blockSum (rowCell 0) 28 2 ≤ (425789534645285926958985378101 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_28) (by simpa only [blockSum_one] using cell_0_29) (by norm_num)

theorem sum_0_30_2 : blockSum (rowCell 0) 30 2 ≤ (1839827777094528805703245353341 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_30) (by simpa only [blockSum_one] using cell_0_31) (by norm_num)

theorem sum_0_28_4 : blockSum (rowCell 0) 28 4 ≤ (708597183135134502707837373149 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_28_2 sum_0_30_2 (by norm_num)

theorem sum_0_24_8 : blockSum (rowCell 0) 24 8 ≤ (6535484491916361402418159883707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_24_4 sum_0_28_4 (by norm_num)

theorem sum_0_16_16 : blockSum (rowCell 0) 16 16 ≤ (10930258059026041649045019906703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_16_8 sum_0_24_8 (by norm_num)

theorem sum_0_0_32 : blockSum (rowCell 0) 0 32 ≤ (1853511425136948197519938726091 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_0_16 sum_0_16_16 (by norm_num)

#print axioms sum_0_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
