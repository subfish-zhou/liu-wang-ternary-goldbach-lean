import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_0_0 : expNegUpper (55229393174453940881 / 676601617795489000 : ℝ) ≤ (3548138164965037783980893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (946077 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_0_1 : expNegUpper (28216318565147528690191 / 346420028311290368000 : ℝ) ≤ (4232899526881578861464439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_0 : rowCell 4 0 ≤ (567400259265506554230517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3548138164965037783980893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4232899526881578861464439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_0_1
  · norm_num [gridPoint]

theorem exp_4_1_0 : expNegUpper (28541251092634068130439 / 350409297769615872000 : ℝ) ≤ (4232877297186608768908653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1889547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_1_1 : expNegUpper (2848070215468719983899 / 35040929776961587200 : ℝ) ≤ (1257823074613602946995031 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (943499 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_1 : rowCell 4 1 ≤ (675551570191514302737737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4232877297186608768908653 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1257823074613602946995031 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_1_1
  · norm_num [gridPoint]

theorem exp_4_2_0 : expNegUpper (2880680161740532968779 / 35442140553369651200 : ℝ) ≤ (5031266472393717810797047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (943499 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_2_1 : expNegUpper (28746837812464031055461 / 354421405533696512000 : ℝ) ≤ (5958743356150884196839951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376901 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_2 : rowCell 4 2 ≤ (801401390534427711437757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5031266472393717810797047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5958743356150884196839951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_2_1
  · norm_num [gridPoint]

theorem exp_4_3_0 : expNegUpper (29074110871972849132189 / 358456351603532288000 : ℝ) ≤ (5958713456049203592287101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376901 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_3_1 : expNegUpper (7253683882704167267167 / 89614087900883072000 : ℝ) ≤ (7032177172439017853767509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_3 : rowCell 4 3 ≤ (473653708066330070116379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5958713456049203592287101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7032177172439017853767509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_3_1
  · norm_num [gridPoint]

theorem exp_4_4_0 : expNegUpper (293431888486752731927 / 3625141359791232000 : ℝ) ≤ (3516071336866326007124419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_4_1 : expNegUpper (1171376212083350424307 / 14500565439164928000 : ℝ) ≤ (330804010914562538732317 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939843 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_4 : rowCell 4 4 ≤ (557926651887364912987303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3516071336866326007124419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (330804010914562538732317 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_4_1
  · norm_num [gridPoint]

theorem exp_4_5_0 : expNegUpper (29614045539851248598387 / 366594758660469248000 : ℝ) ≤ (4135030300900706933543347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939843 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_5_1 : expNegUpper (14777928559301976200773 / 183297379330234624000 : ℝ) ≤ (4846328844368148946672049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_5 : rowCell 4 5 ≤ (163732194515715512068253 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4135030300900706933543347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4846328844368148946672049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_5_1
  · norm_num [gridPoint]

theorem exp_4_6_0 : expNegUpper (14943345468919711039157 / 185349109823785216000 : ℝ) ≤ (9692612220259785010101247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (469339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_6_1 : expNegUpper (5965820194543178235869 / 74139643929514086400 : ℝ) ≤ (11321678677799032806033691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_6 : rowCell 4 6 ≤ (383095243078356929967923 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9692612220259785010101247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11321678677799032806033691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_6_1
  · norm_num [gridPoint]

theorem exp_4_7_0 : expNegUpper (6032227006995688072309 / 74964903788085350400 : ℝ) ≤ (56608133668251137558073 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875079 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_7_1 : expNegUpper (3763018357094777958767 / 46853064867553344000 : ℝ) ≤ (205948592067769659796887 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_7 : rowCell 4 7 ≤ (1786732400585069870691551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (56608133668251137558073 / 5000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (205948592067769659796887 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_7_1
  · norm_num [gridPoint]

theorem exp_4_8_0 : expNegUpper (3804673477950868772143 / 47371707067379776000 : ℝ) ≤ (823790671214238593598761 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872853 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_8_1 : expNegUpper (30381004763069596602983 / 378973656539038208000 : ℝ) ≤ (15295034176908956759098853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935339 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_8 : rowCell 4 8 ≤ (2076472527722444600117657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (823790671214238593598761 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15295034176908956759098853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_8_1
  · norm_num [gridPoint]

theorem exp_4_9_0 : expNegUpper (1228618371842543930167 / 15325825297736192000 : ℝ) ≤ (1529496702600012079222563 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935339 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_9_1 : expNegUpper (613193693679773134139 / 7662912648868096000 : ℝ) ≤ (17691673212031084393000703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233569 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_9 : rowCell 4 9 ≤ (2405415442591824338267613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1529496702600012079222563 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17691673212031084393000703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_9_1
  · norm_num [gridPoint]

theorem exp_4_10_0 : expNegUpper (673812161841022420037 / 8420444492467968000 : ℝ) ≤ (17691597216764017669717253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233569 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_10_1 : expNegUpper (1345225939645828291787 / 16840888984935936000 : ℝ) ≤ (20399372287579635230226271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_10 : rowCell 4 10 ≤ (555525543722430645642907 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17691597216764017669717253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20399372287579635230226271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_10_1
  · norm_num [gridPoint]

theorem exp_4_11_0 : expNegUpper (31277098261815896108789 / 391558099169403392000 : ℝ) ≤ (20399286543897747461100811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_11_1 : expNegUpper (62445101078008850689 / 783116198338806784 : ℝ) ≤ (23448565591637793765054951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466111 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_11 : rowCell 4 11 ≤ (3197424772277904686424099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20399286543897747461100811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23448565591637793765054951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_11_1
  · norm_num [gridPoint]

theorem exp_4_12_0 : expNegUpper (63121371479577678689 / 791597179982070784 : ℝ) ≤ (23448469137640336974289983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466111 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_12_1 : expNegUpper (31506756457778427336211 / 395798589991035392000 : ℝ) ≤ (2687132053767538330314749 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93123 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_12 : rowCell 4 12 ≤ (1834682136155029369549089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23448469137640336974289983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2687132053767538330314749 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_12_1
  · norm_num [gridPoint]

theorem exp_4_13_0 : expNegUpper (31846131870944507757899 / 400061919118422528000 : ℝ) ≤ (13435606176969539908327939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93123 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_13_1 : expNegUpper (15896412180257351707649 / 200030959559211264000 : ℝ) ≤ (7675314956300565608005007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_13 : rowCell 4 13 ≤ (1049559099142740031018281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13435606176969539908327939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7675314956300565608005007 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_13_1
  · norm_num [gridPoint]

theorem exp_4_14_0 : expNegUpper (642668932952430961561 / 8086961731031296000 : ℝ) ≤ (7675284708901119862776299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_14_1 : expNegUpper (1283230569582076012433 / 16173923462062592000 : ℝ) ≤ (874336503390432102053951 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1858629 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_14 : rowCell 4 14 ≤ (478905076150400420389873 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7675284708901119862776299 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (874336503390432102053951 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_14_1
  · norm_num [gridPoint]

theorem exp_4_15_0 : expNegUpper (32422640062158607034017 / 408657092290462208000 : ℝ) ≤ (34973325208690351370719721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185863 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_15_1 : expNegUpper (2023161630451791546991 / 25541068268153888000 : ℝ) ≤ (1986216330216893222095789 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_15 : rowCell 4 15 ≤ (217880795255102730583801 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34973325208690351370719721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1986216330216893222095789 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_15_1
  · norm_num [gridPoint]

theorem exp_4_16_0 : expNegUpper (2044607631680895709679 / 25811808520944672000 : ℝ) ≤ (99310441387948908404237 / 2500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_16_1 : expNegUpper (6532459979176728693491 / 82597787267022950400 : ℝ) ≤ (44991442480163245527528027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28984 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_16 : rowCell 4 16 ≤ (617753905174617469000699 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (99310441387948908404237 / 2500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44991442480163245527528027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_16_1
  · norm_num [gridPoint]

theorem exp_4_17_0 : expNegUpper (6601340554833473553931 / 83468723737104486400 : ℝ) ≤ (1799651042916932973507101 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28984 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_17_1 : expNegUpper (16477957828927741593343 / 208671809342761216000 : ℝ) ≤ (12703348420047505179631497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_17 : rowCell 4 17 ≤ (698616259290500643426931 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1799651042916932973507101 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12703348420047505179631497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_17_1
  · norm_num [gridPoint]

theorem exp_4_18_0 : expNegUpper (16650796028158181503727 / 210860569670842624000 : ℝ) ≤ (25406604815573434746236973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853213 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_18_1 : expNegUpper (33251443365482830638613 / 421721139341685248000 : ℝ) ≤ (7153696033720317417219479 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_18 : rowCell 4 18 ≤ (984822054277198055024669 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25406604815573434746236973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7153696033720317417219479 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_18_1
  · norm_num [gridPoint]

theorem exp_4_19_0 : expNegUpper (43352774123458017803 / 549834191359488000 : ℝ) ≤ (14307341312749489168377197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462873 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_19_1 : expNegUpper (10822223551969139533 / 137458547839872000 : ℝ) ≤ (12855986247513176775533271 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462453 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_19 : rowCell 4 19 ≤ (8860567068454639197067187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14307341312749489168377197 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12855986247513176775533271 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_19_1
  · norm_num [gridPoint]

theorem exp_4_20_0 : expNegUpper (8474284108649204217083 / 107636173892819072000 : ℝ) ≤ (64279707881239266182379241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (462453 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_20_1 : expNegUpper (33848274587058635656811 / 430544695571276288000 : ℝ) ≤ (3600238764557434373965211 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_20 : rowCell 4 20 ≤ (2484496739005219943328019 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (64279707881239266182379241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3600238764557434373965211 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_20_1
  · norm_num [gridPoint]

theorem exp_4_21_0 : expNegUpper (34197811515405568949539 / 434990731144704512000 : ℝ) ≤ (18001132548591264703445487 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848173 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_21_1 : expNegUpper (3414959808568438668121 / 43499073114470451200 : ℝ) ≤ (80444448762506328853157279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_21 : rowCell 4 21 ≤ (5558358255707296576405283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18001132548591264703445487 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80444448762506328853157279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_21_1
  · norm_num [gridPoint]

theorem exp_4_22_0 : expNegUpper (3450043518044486677001 / 43945960502388787200 : ℝ) ≤ (80444180492765501809252303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1846573 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_22_1 : expNegUpper (34452873499320232354561 / 439459605023887872000 : ℝ) ≤ (8963906208108490008417337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_22 : rowCell 4 22 ≤ (3100655714412105312447263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80444180492765501809252303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8963906208108490008417337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_22_1
  · norm_num [gridPoint]

theorem exp_4_23_0 : expNegUpper (34805017422053357058809 / 443951317208826368000 : ℝ) ≤ (44819384591145909369762751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845013 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_23_1 : expNegUpper (4344763852538102425741 / 55493914651103296000 : ℝ) ≤ (99628174636628317087592561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843491 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_23 : rowCell 4 23 ≤ (6900757793897746807786491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44819384591145909369762751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (99628174636628317087592561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_23_1
  · norm_num [gridPoint]

theorem exp_4_24_0 : expNegUpper (7022313646513937309 / 89693173539904000 : ℝ) ≤ (12453481954454673596423843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1843491 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_24_1 : expNegUpper (56104512065562871303 / 717545388319232000 : ℝ) ≤ (55225232105235283453178641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_24 : rowCell 4 24 ≤ (1914887478177334858204727 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12453481954454673596423843 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55225232105235283453178641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_24_1
  · norm_num [gridPoint]

theorem exp_4_25_0 : expNegUpper (35420097604332501957647 / 453003256495968768000 : ℝ) ≤ (110450117624129649595128649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_25_1 : expNegUpper (17687255576837402279483 / 226501628247984384000 : ℝ) ≤ (61071690747460463935851161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_25 : rowCell 4 25 ≤ (4240231731620758220221127 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (110450117624129649595128649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (61071690747460463935851161 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_25_1
  · norm_num [gridPoint]

theorem exp_4_26_0 : expNegUpper (17865307764840225012907 / 228781741799086336000 : ℝ) ≤ (12214300583757371399803163 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (920279 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_26_1 : expNegUpper (7137138830147499223753 / 91512696719634534400 : ℝ) ≤ (16842849067517426442685143 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_26 : rowCell 4 26 ≤ (18732343213537321090977499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12214300583757371399803163 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16842849067517426442685143 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_26_1
  · norm_num [gridPoint]

theorem exp_4_27_0 : expNegUpper (7208626400190435495713 / 92429309801226342400 : ℝ) ≤ (134742386331538344480083403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839147 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_27_1 : expNegUpper (8999719756125878993209 / 115536637251532928000 : ℝ) ≤ (9267663266275267728293729 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459443 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_27 : rowCell 4 27 ≤ (4127687435519325778379501 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (134742386331538344480083403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9267663266275267728293729 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_27_1
  · norm_num [gridPoint]

theorem exp_4_28_0 : expNegUpper (9089414252621582761241 / 116688113179961472000 : ℝ) ≤ (148282174033979963934616197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459443 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_28_1 : expNegUpper (36314075767311510850243 / 466752452719845888000 : ℝ) ≤ (40698608097830364251780047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114777 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_28 : rowCell 4 28 ≤ (4536797124684312969363359 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148282174033979963934616197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40698608097830364251780047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_28_1
  · norm_num [gridPoint]

theorem exp_4_29_0 : expNegUpper (1466968022024862298163 / 18855247789572608000 : ℝ) ≤ (2543655635980450615850703 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114777 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_29_1 : expNegUpper (732625887430002549601 / 9427623894786304000 : ℝ) ≤ (35661429502231512010023219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_29 : rowCell 4 29 ≤ (6218349817246241395121641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2543655635980450615850703 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35661429502231512010023219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_29_1
  · norm_num [gridPoint]

theorem exp_4_30_0 : expNegUpper (18496386306848251717481 / 238016387532269824000 : ℝ) ≤ (89153320473577100297214147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1835127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_30_1 : expNegUpper (36950544829408012591321 / 476032775064539648000 : ℝ) ≤ (974232914592476039480623 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366771 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_30 : rowCell 4 30 ≤ (13605334169566360830760779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (89153320473577100297214147 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (974232914592476039480623 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_30_1
  · norm_num [gridPoint]

theorem exp_4_31_0 : expNegUpper (37313383192049815716689 / 480707193695519232000 : ℝ) ≤ (6088938753305702265742527 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (366771 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_31_1 : expNegUpper (232948982083586330707 / 3004419960596995200 : ℝ) ≤ (212435128290866940480471053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1832617 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_31 : rowCell 4 31 ≤ (2969930871615840655951717 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6088938753305702265742527 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (212435128290866940480471053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_31_1
  · norm_num [gridPoint]

theorem sum_4_0_2 : blockSum (rowCell 4) 0 2 ≤ (621475914728510428484127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_0) (by simpa only [blockSum_one] using cell_4_1) (by norm_num)

theorem sum_4_2_2 : blockSum (rowCell 4) 2 2 ≤ (349741761333417570334103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_2) (by simpa only [blockSum_one] using cell_4_3) (by norm_num)

theorem sum_4_0_4 : blockSum (rowCell 4) 0 4 ≤ (2991660636124108708638769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_0_2 sum_4_2_2 (by norm_num)

theorem sum_4_4_2 : blockSum (rowCell 4) 4 2 ≤ (242571085990045392252063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_4) (by simpa only [blockSum_one] using cell_4_5) (by norm_num)

theorem sum_4_6_2 : blockSum (rowCell 4) 6 2 ≤ (3319113372898497590563243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_6) (by simpa only [blockSum_one] using cell_4_7) (by norm_num)

theorem sum_4_4_4 : blockSum (rowCell 4) 4 4 ≤ (5744824232798951513083873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_4_2 sum_4_6_2 (by norm_num)

theorem sum_4_0_8 : blockSum (rowCell 4) 0 8 ≤ (4368242434461530110861321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_0_4 sum_4_4_4 (by norm_num)

theorem sum_4_8_2 : blockSum (rowCell 4) 8 2 ≤ (448188797031426893838527 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_8) (by simpa only [blockSum_one] using cell_4_9) (by norm_num)

theorem sum_4_10_2 : blockSum (rowCell 4) 10 2 ≤ (2987526245445028957319317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_10) (by simpa only [blockSum_one] using cell_4_11) (by norm_num)

theorem sum_4_8_4 : blockSum (rowCell 4) 8 4 ≤ (326779389412635214156997 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_8_2 sum_4_10_2 (by norm_num)

theorem sum_4_12_2 : blockSum (rowCell 4) 12 2 ≤ (3933800334440509431585651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_12) (by simpa only [blockSum_one] using cell_4_13) (by norm_num)

theorem sum_4_14_2 : blockSum (rowCell 4) 14 2 ≤ (2047214128576314493698751 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_14) (by simpa only [blockSum_one] using cell_4_15) (by norm_num)

theorem sum_4_12_4 : blockSum (rowCell 4) 12 4 ≤ (18103671311762591331665057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_12_2 sum_4_14_2 (by norm_num)

theorem sum_4_8_8 : blockSum (rowCell 4) 8 8 ≤ (28560611772966918184688961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_8_4 sum_4_12_4 (by norm_num)

theorem sum_4_0_16 : blockSum (rowCell 4) 0 16 ≤ (37297096641889978406411603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_0_8 sum_4_8_8 (by norm_num)

theorem sum_4_16_2 : blockSum (rowCell 4) 16 2 ≤ (131637016446511811242763 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_16) (by simpa only [blockSum_one] using cell_4_17) (by norm_num)

theorem sum_4_18_2 : blockSum (rowCell 4) 18 2 ≤ (16739143502672223637264539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_18) (by simpa only [blockSum_one] using cell_4_19) (by norm_num)

theorem sum_4_16_4 : blockSum (rowCell 4) 16 4 ≤ (29902845147323404761540839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_16_2 sum_4_18_2 (by norm_num)

theorem sum_4_20_2 : blockSum (rowCell 4) 20 2 ≤ (10527351733717736463061321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_20) (by simpa only [blockSum_one] using cell_4_21) (by norm_num)

theorem sum_4_22_2 : blockSum (rowCell 4) 22 2 ≤ (13102069222721957432681017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_22) (by simpa only [blockSum_one] using cell_4_23) (by norm_num)

theorem sum_4_20_4 : blockSum (rowCell 4) 20 4 ≤ (11814710478219846947871169 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_20_2 sum_4_22_2 (by norm_num)

theorem sum_4_16_8 : blockSum (rowCell 4) 16 8 ≤ (15432337412040558510605103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_16_4 sum_4_20_4 (by norm_num)

theorem sum_4_24_2 : blockSum (rowCell 4) 24 2 ≤ (8070006687975427936630581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_24) (by simpa only [blockSum_one] using cell_4_25) (by norm_num)

theorem sum_4_26_2 : blockSum (rowCell 4) 26 2 ≤ (9842695097783487495718751 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_26) (by simpa only [blockSum_one] using cell_4_27) (by norm_num)

theorem sum_4_24_4 : blockSum (rowCell 4) 24 4 ≤ (4478175446439728858087333 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_24_2 sum_4_26_2 (by norm_num)

theorem sum_4_28_2 : blockSum (rowCell 4) 28 2 ≤ (47557384892406530427303359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_28) (by simpa only [blockSum_one] using cell_4_29) (by norm_num)

theorem sum_4_30_2 : blockSum (rowCell 4) 30 2 ≤ (7113747131911391027629841 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_30) (by simpa only [blockSum_one] using cell_4_31) (by norm_num)

theorem sum_4_28_4 : blockSum (rowCell 4) 28 4 ≤ (104467361947697658648342087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_28_2 sum_4_30_2 (by norm_num)

theorem sum_4_24_8 : blockSum (rowCell 4) 24 8 ≤ (35223633818146664075547883 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_24_4 sum_4_28_4 (by norm_num)

theorem sum_4_16_16 : blockSum (rowCell 4) 16 16 ≤ (25327985615093611293076493 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_16_8 sum_4_24_8 (by norm_num)

theorem sum_4_0_32 : blockSum (rowCell 4) 0 32 ≤ (290576952792826091337176533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_0_16 sum_4_16_16 (by norm_num)

#print axioms sum_4_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
