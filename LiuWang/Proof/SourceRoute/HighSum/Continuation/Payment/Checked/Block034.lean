import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_64_0 : expNegUpper (9746927823189946981 / 134953187093016000 : ℝ) ≤ (860513884039840598476516957 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (351627 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_64_1 : expNegUpper (623703759790243871501 / 8637003973953024000 : ℝ) ≤ (21762417016339157921473238631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_64 : rowCell 2 64 ≤ (3155671139556186224975906391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (860513884039840598476516957 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21762417016339157921473238631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_64_1
  · norm_num [gridPoint]

theorem exp_2_65_0 : expNegUpper (47171410111530811812167 / 653226219073131008000 : ℝ) ≤ (10881193540451330078172483791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757977 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_65_1 : expNegUpper (23582366758302253817703 / 326613109536565504000 : ℝ) ≤ (21985960049306488939449049713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439459 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_65 : rowCell 2 65 ≤ (1595084388945237974673845247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10881193540451330078172483791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21985960049306488939449049713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_65_1
  · norm_num [gridPoint]

theorem exp_2_66_0 : expNegUpper (23779977459440439966807 / 329349989202770176000 : ℝ) ≤ (5496482576989769221239124413 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439459 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_66_1 : expNegUpper (9510815325370255127201 / 131739995681108070400 : ℝ) ≤ (2218301261443284515626429047 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878857 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_66 : rowCell 2 66 ≤ (6441678001870951583476557559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5496482576989769221239124413 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2218301261443284515626429047 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_66_1
  · norm_num [gridPoint]

theorem exp_2_67_0 : expNegUpper (3196726531046706440147 / 44279771736246988800 : ℝ) ≤ (1386436443884767142711370099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878857 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_67_1 : expNegUpper (3995485108945603424453 / 55349714670308736000 : ℝ) ≤ (22353184073201877577907737907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_67 : rowCell 2 67 ≤ (202976082711863315285300303 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1386436443884767142711370099 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22353184073201877577907737907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_67_1
  · norm_num [gridPoint]

theorem exp_2_68_0 : expNegUpper (1726580330154593162393 / 23918428999558016000 : ℝ) ≤ (22353154823694775550788429031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757609 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_68_1 : expNegUpper (6905711078633007248109 / 95673715998232064000 : ℝ) ≤ (44992374199011837236423380759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_68 : rowCell 2 68 ≤ (6540908614740857488854312337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22353154823694775550788429031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44992374199011837236423380759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_68_1
  · norm_num [gridPoint]

theorem exp_2_69_0 : expNegUpper (1949600749884142499883 / 27010331449491968000 : ℝ) ≤ (11248079072545692951095590997 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_69_1 : expNegUpper (974731106968827025901 / 13505165724745984000 : ℝ) ≤ (45223674619008650297904579781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_69 : rowCell 2 69 ≤ (1644657777631892744091764741 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11248079072545692951095590997 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45223674619008650297904579781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_69_1
  · norm_num [gridPoint]

theorem exp_2_70_0 : expNegUpper (8189702744394017530247 / 113470566465454848000 : ℝ) ≤ (22611808681047530211577185953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_70_1 : expNegUpper (16378521564572263165787 / 226941132930909696000 : ℝ) ≤ (9080020908370902791492999251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878699 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_70 : rowCell 2 70 ≤ (1321672644197230208706099383 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22611808681047530211577185953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9080020908370902791492999251 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_70_1
  · norm_num [gridPoint]

theorem exp_2_71_0 : expNegUpper (49538852394448883329289 / 686411349653914112000 : ℝ) ≤ (45400047995526276900644656729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878699 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_71_1 : expNegUpper (1238425389464900301819 / 17160283741347852800 : ℝ) ≤ (2845106239755212955627419741 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_71 : rowCell 2 71 ≤ (1657523884847198908252567899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45400047995526276900644656729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2845106239755212955627419741 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_71_1
  · norm_num [gridPoint]

theorem exp_2_72_0 : expNegUpper (1248548413092413591739 / 17300553470521356800 : ℝ) ≤ (4552164405582562211793130073 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_72_1 : expNegUpper (49940917995417665750311 / 692022138820854272000 : ℝ) ≤ (22794346402579916409743763767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757341 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_72 : rowCell 2 72 ≤ (1328769524169266583131250259 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4552164405582562211793130073 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22794346402579916409743763767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_72_1
  · norm_num [gridPoint]

theorem exp_2_73_0 : expNegUpper (16782492948815244310453 / 232551922097849856000 : ℝ) ≤ (45588637843168688843751530383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757341 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_73_1 : expNegUpper (8391213656086732876513 / 116275961048924928000 : ℝ) ≤ (22800753414541722191744813047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_73 : rowCell 2 73 ≤ (166241681953655738286409287 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45588637843168688843751530383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22800753414541722191744813047 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_73_1
  · norm_num [gridPoint]

theorem exp_2_74_0 : expNegUpper (1624175659361123131 / 22505991426304000 : ℝ) ≤ (45601452734182042004475886411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757337 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_74_1 : expNegUpper (3248391513231542613 / 45011982852608000 : ℝ) ≤ (45560750019811717349817626993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757349 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_74 : rowCell 2 74 ≤ (6647629728362761723383252871 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45601452734182042004475886411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45560750019811717349817626993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_74_1
  · norm_num [gridPoint]

theorem exp_2_75_0 : expNegUpper (7309425434543326447971 / 101284505165172224000 : ℝ) ≤ (22780348418692736180151267133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757349 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_75_1 : expNegUpper (1827408370032988595947 / 25321126291293056000 : ℝ) ≤ (45467207969825203092091535907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_75 : rowCell 2 75 ≤ (3318918300712513841164901179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22780348418692736180151267133 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45467207969825203092091535907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_75_1
  · norm_num [gridPoint]

theorem exp_2_76_0 : expNegUpper (4298246241590745128047 / 59557806545513856000 : ℝ) ≤ (45467155741776341764705997119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_76_1 : expNegUpper (3438749521926768404221 / 47646245236411084800 : ℝ) ≤ (45321835677416269615770232611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_76 : rowCell 2 76 ≤ (6620414822522003402726113819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45467155741776341764705997119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45321835677416269615770232611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_76_1
  · norm_num [gridPoint]

theorem exp_2_77_0 : expNegUpper (10398885983846142755023 / 144083731848376422400 : ℝ) ≤ (45321784442136809365055005651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757421 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_77_1 : expNegUpper (25998776395257518093793 / 360209329620941056000 : ℝ) ≤ (22562874367773996179714817759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_77 : rowCell 2 77 ≤ (12881865978071025523317323 / 1953125000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45321784442136809365055005651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22562874367773996179714817759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_77_1
  · norm_num [gridPoint]

theorem exp_2_78_0 : expNegUpper (26206206547283624290257 / 363083239121676544000 : ℝ) ≤ (45125698527910501813203401153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_78_1 : expNegUpper (52416374238102857788393 / 726166478243353088000 : ℝ) ≤ (44880213873423598352296554221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439389 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_78 : rowCell 2 78 ≤ (1640827999248051414418468547 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45125698527910501813203401153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44880213873423598352296554221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_78_1
  · norm_num [gridPoint]

theorem exp_2_79_0 : expNegUpper (704438858899162569091 / 9759161807341056000 : ℝ) ≤ (22440082362394470757171116119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439389 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_79_1 : expNegUpper (44031430970003031329 / 609947612958816000 : ℝ) ≤ (44586638941257451134137271739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_79 : rowCell 2 79 ≤ (6523999703659521665483020549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22440082362394470757171116119 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44586638941257451134137271739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_79_1
  · norm_num [gridPoint]

theorem exp_2_80_0 : expNegUpper (3328496492511199550507 / 46108164447722528000 : ℝ) ≤ (11146647719874660763828314217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_80_1 : expNegUpper (53261591560556022335871 / 737730631163560448000 : ℝ) ≤ (44246562429184102854140778981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_80 : rowCell 2 80 ≤ (40486208439408260008574477 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11146647719874660763828314217 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44246562429184102854140778981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_80_1
  · norm_num [gridPoint]

theorem exp_2_81_0 : expNegUpper (1731661660488125667369 / 23985385970396672000 : ℝ) ≤ (22123257739362669401628462083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757751 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_81_1 : expNegUpper (173187120709995673357 / 2398538597039667200 : ℝ) ≤ (21930821305414340041683766831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_81 : rowCell 2 81 ≤ (6424926047563562640901498917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22123257739362669401628462083 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21930821305414340041683766831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_81_1
  · norm_num [gridPoint]

theorem exp_2_82_0 : expNegUpper (257664891403018800247 / 3568505415746611200 : ℝ) ≤ (43861596792698546451807795781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1757871 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_82_1 : expNegUpper (2576998796903342549441 / 35685054157466112000 : ℝ) ≤ (43433646400843056323638249093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_82 : rowCell 2 82 ≤ (3182823781496555185959634579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43861596792698546451807795781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43433646400843056323638249093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_82_1
  · norm_num [gridPoint]

theorem exp_2_83_0 : expNegUpper (54540301031023996627469 / 755248147837035008000 : ℝ) ≤ (10858400433185222281862995759 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_83_1 : expNegUpper (13637125874377318364427 / 188812036959258752000 : ℝ) ≤ (21482219006873495216622059959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (351631 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_83 : rowCell 2 83 ≤ (6300222681552730912770252641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10858400433185222281862995759 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21482219006873495216622059959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_83_1
  · norm_num [gridPoint]

theorem exp_2_84_0 : expNegUpper (549735429766406881443 / 7611329966730368000 : ℝ) ≤ (8592878902024263182663621553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (351631 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_84_1 : expNegUpper (2199304148002181809123 / 30445319866921472000 : ℝ) ≤ (42455967508765472505784083969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879159 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_84 : rowCell 2 84 ≤ (6228929543273725955119902109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8592878902024263182663621553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42455967508765472505784083969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_84_1
  · norm_num [gridPoint]

theorem exp_2_85_0 : expNegUpper (18469787674607556443809 / 255680227938264576000 : ℝ) ≤ (42455925180903443504369841417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879159 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_85_1 : expNegUpper (9236547555824109263071 / 127840113969132288000 : ℝ) ≤ (20955129651045146341703866793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54953 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_85 : rowCell 2 85 ≤ (384503623140235917656099811 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42455925180903443504369841417 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20955129651045146341703866793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_85_1
  · norm_num [gridPoint]

theorem exp_2_86_0 : expNegUpper (27923885582454293458957 / 386485604631152896000 : ℝ) ≤ (10477554539554255913294087103 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54953 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_86_1 : expNegUpper (2234342335780730049513 / 30918848370492231680 : ℝ) ≤ (41329400724185201838847150539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54959 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_86 : rowCell 2 86 ≤ (3034953897249929970563909517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10477554539554255913294087103 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41329400724185201838847150539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_86_1
  · norm_num [gridPoint]

theorem exp_2_87_0 : expNegUpper (2251551095689483505313 / 31156982920622919680 : ℝ) ≤ (5166170096196487989529743649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (54959 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_87_1 : expNegUpper (7037554108889247366917 / 97365571626946624000 : ℝ) ≤ (10178882673867822216511667431 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_87 : rowCell 2 87 ≤ (2991393598919062621213854873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5166170096196487989529743649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10178882673867822216511667431 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_87_1
  · norm_num [gridPoint]

theorem exp_2_88_0 : expNegUpper (2363849654089450758551 / 32704198961441472000 : ℝ) ≤ (40715491932551113761313435287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758893 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_88_1 : expNegUpper (18914972919023495133341 / 261633591691531776000 : ℝ) ≤ (40070828589044158514187544423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1759113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_88 : rowCell 2 88 ≤ (5891011073894570875081966461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40715491932551113761313435287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40070828589044158514187544423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_88_1
  · norm_num [gridPoint]

theorem exp_2_89_0 : expNegUpper (326734994714151002081 / 4519427516796416000 : ℝ) ≤ (10017697754383668836235033083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1759113 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_89_1 : expNegUpper (163405788699218335317 / 2259713758398208000 : ℝ) ≤ (39397503344058528436605299471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879673 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_89 : rowCell 2 89 ≤ (579489942214309191364431537 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10017697754383668836235033083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39397503344058528436605299471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_89_1
  · norm_num [gridPoint]

theorem exp_2_90_0 : expNegUpper (28813742257532277919371 / 398460847054952704000 : ℝ) ≤ (39397466961089780340829321733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879673 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_90_1 : expNegUpper (57641764726420421547181 / 796921694109905408000 : ℝ) ≤ (38697782888139087498885025253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219949 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_90 : rowCell 2 90 ≤ (2847387891353402729716459963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39397466961089780340829321733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38697782888139087498885025253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_90_1
  · norm_num [gridPoint]

theorem exp_2_91_0 : expNegUpper (19359661003583285452663 / 267655470362064384000 : ℝ) ≤ (4837218461048275521385275493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (219949 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_91_1 : expNegUpper (968235746574852411463 / 13382773518103219200 : ℝ) ≤ (37973903921706975547949739461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439963 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_91 : rowCell 2 91 ≤ (5590965720094988108202963131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4837218461048275521385275493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37973903921706975547949739461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_91_1
  · norm_num [gridPoint]

theorem exp_2_92_0 : expNegUpper (2926656477718548682549 / 40451698318411801600 : ℝ) ≤ (4746733737190794125517042001 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (439963 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_92_1 : expNegUpper (58549176241277233511811 / 809033966368236032000 : ℝ) ≤ (9307025527878623754583101177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (440031 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_92 : rowCell 2 92 ≤ (68547442039637318880441447 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4746733737190794125517042001 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9307025527878623754583101177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_92_1
  · norm_num [gridPoint]

theorem exp_2_93_0 : expNegUpper (58989934138266554446779 / 815124359956034048000 : ℝ) ≤ (9307017313270648542314089377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (440031 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_93_1 : expNegUpper (29503434529558667374169 / 407562179978017024000 : ℝ) ≤ (18231301367509420598864777097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176041 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_93 : rowCell 2 93 ≤ (41981171936214617006593361 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9307017313270648542314089377 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18231301367509420598864777097 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_93_1
  · norm_num [gridPoint]

theorem exp_2_94_0 : expNegUpper (396329378365168303163 / 5474917278997248000 : ℝ) ≤ (4557821378809087682636650207 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176041 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_94_1 : expNegUpper (792896443204667935019 / 10949834557994496000 : ℝ) ≤ (8919902952889301574074053263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_94 : rowCell 2 94 ≤ (5260672788083218009914086901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4557821378809087682636650207 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8919902952889301574074053263 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_94_1
  · norm_num [gridPoint]

theorem exp_2_95_0 : expNegUpper (59911557396235693463057 / 827373662048895488000 : ℝ) ≤ (35679581247135818790664071661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1760709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_95_1 : expNegUpper (1872821211791067542973 / 25855426939027984000 : ℝ) ≤ (3488130775066491143723999403 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (88051 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_95 : rowCell 2 95 ≤ (5145363420268338209812328603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35679581247135818790664071661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3488130775066491143723999403 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_95_1
  · norm_num [gridPoint]

theorem sum_2_64_2 : blockSum (rowCell 2) 64 2 ≤ (1269167983489332434864719377 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_64) (by simpa only [blockSum_one] using cell_2_65) (by norm_num)

theorem sum_2_66_2 : blockSum (rowCell 2) 66 2 ≤ (2587382529730115534521233451 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_66) (by simpa only [blockSum_one] using cell_2_67) (by norm_num)

theorem sum_2_64_4 : blockSum (rowCell 2) 64 4 ≤ (1025143699341756080850134441 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_64_2 sum_2_66_2 (by norm_num)

theorem sum_2_68_2 : blockSum (rowCell 2) 68 2 ≤ (13119539725268428465221371301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_68) (by simpa only [blockSum_one] using cell_2_69) (by norm_num)

theorem sum_2_70_2 : blockSum (rowCell 2) 70 2 ≤ (13238458760374946676540768511 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_70) (by simpa only [blockSum_one] using cell_2_71) (by norm_num)

theorem sum_2_68_4 : blockSum (rowCell 2) 68 4 ≤ (6589499621410843785440534953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_68_2 sum_2_70_2 (by norm_num)

theorem sum_2_64_8 : blockSum (rowCell 2) 64 8 ≤ (51986590969187277163015500837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_64_4 sum_2_68_4 (by norm_num)

theorem sum_2_72_2 : blockSum (rowCell 2) 72 2 ≤ (531740595959702497884504911 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_72) (by simpa only [blockSum_one] using cell_2_73) (by norm_num)

theorem sum_2_74_2 : blockSum (rowCell 2) 74 2 ≤ (13285466329787789405713055229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_74) (by simpa only [blockSum_one] using cell_2_75) (by norm_num)

theorem sum_2_72_4 : blockSum (rowCell 2) 72 4 ≤ (6644745307195087963206419501 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_72_2 sum_2_74_2 (by norm_num)

theorem sum_2_76_2 : blockSum (rowCell 2) 76 2 ≤ (2643186040658873694132916639 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_76) (by simpa only [blockSum_one] using cell_2_77) (by norm_num)

theorem sum_2_78_2 : blockSum (rowCell 2) 78 2 ≤ (13087311700651727323156894737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_78) (by simpa only [blockSum_one] using cell_2_79) (by norm_num)

theorem sum_2_76_4 : blockSum (rowCell 2) 76 4 ≤ (6575810475986523948455369483 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_76_2 sum_2_78_2 (by norm_num)

theorem sum_2_72_8 : blockSum (rowCell 2) 72 8 ≤ (1652569472897701488957723623 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_72_4 sum_2_76_4 (by norm_num)

theorem sum_2_64_16 : blockSum (rowCell 2) 64 16 ≤ (104868814101913724809662656773 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_64_8 sum_2_72_8 (by norm_num)

theorem sum_2_80_2 : blockSum (rowCell 2) 80 2 ≤ (12902719397868884242273415237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_80) (by simpa only [blockSum_one] using cell_2_81) (by norm_num)

theorem sum_2_82_2 : blockSum (rowCell 2) 82 2 ≤ (12665870244545841284689521799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_82) (by simpa only [blockSum_one] using cell_2_83) (by norm_num)

theorem sum_2_80_4 : blockSum (rowCell 2) 80 4 ≤ (6392147410603681381740734259 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_80_2 sum_2_82_2 (by norm_num)

theorem sum_2_84_2 : blockSum (rowCell 2) 84 2 ≤ (2476197502703500127523499817 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_84) (by simpa only [blockSum_one] using cell_2_85) (by norm_num)

theorem sum_2_86_2 : blockSum (rowCell 2) 86 2 ≤ (602634749616899259177776439 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_86) (by simpa only [blockSum_one] using cell_2_87) (by norm_num)

theorem sum_2_84_4 : blockSum (rowCell 2) 84 4 ≤ (4886736501171097164234605573 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_84_2 sum_2_86_2 (by norm_num)

theorem sum_2_80_8 : blockSum (rowCell 2) 80 8 ≤ (50002272148270211348135964901 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_80_4 sum_2_84_4 (by norm_num)

theorem sum_2_88_2 : blockSum (rowCell 2) 88 2 ≤ (11685910496037662788726281831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_88) (by simpa only [blockSum_one] using cell_2_89) (by norm_num)

theorem sum_2_90_2 : blockSum (rowCell 2) 90 2 ≤ (11285741502801793567635883057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_90) (by simpa only [blockSum_one] using cell_2_91) (by norm_num)

theorem sum_2_88_4 : blockSum (rowCell 2) 88 4 ≤ (2871456499854932044545270611 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_88_2 sum_2_90_2 (by norm_num)

theorem sum_2_92_2 : blockSum (rowCell 2) 92 2 ≤ (678586585687903530454954123 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_92) (by simpa only [blockSum_one] using cell_2_93) (by norm_num)

theorem sum_2_94_2 : blockSum (rowCell 2) 94 2 ≤ (650377263021972263732900969 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_94) (by simpa only [blockSum_one] using cell_2_95) (by norm_num)

theorem sum_2_92_4 : blockSum (rowCell 2) 92 4 ≤ (332240962177468948546963773 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_92_2 sum_2_94_2 (by norm_num)

theorem sum_2_88_8 : blockSum (rowCell 2) 88 8 ≤ (1105876839454936726584196159 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_88_4 sum_2_92_4 (by norm_num)

theorem sum_2_80_16 : blockSum (rowCell 2) 80 16 ≤ (94237345726467680411503811261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_80_8 sum_2_88_8 (by norm_num)

theorem sum_2_64_32 : blockSum (rowCell 2) 64 32 ≤ (99553079914190702610583234017 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_64_16 sum_2_80_16 (by norm_num)

#print axioms sum_2_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
