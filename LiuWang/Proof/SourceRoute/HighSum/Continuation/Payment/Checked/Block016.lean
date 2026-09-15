import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_0_0 : expNegUpper (49432822400949940881 / 676601617795489000 : ℝ) ≤ (9325055056512527919119916397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (353931 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_0_1 : expNegUpper (25265465042527112690191 / 346420028311290368000 : ℝ) ≤ (21184498315463210781515351843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_0 : rowCell 1 0 ≤ (2904775435511374371839589251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9325055056512527919119916397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21184498315463210781515351843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_0_1
  · norm_num [gridPoint]

theorem exp_1_1_0 : expNegUpper (8518805381062129376813 / 116803099256538624000 : ℝ) ≤ (21184403991796314653586387159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_1_1 : expNegUpper (850428597288438394633 / 11680309925653862400 : ℝ) ≤ (11994218867946699872150373619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883089 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_1 : rowCell 1 1 ≤ (411755525469765461890213649 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21184403991796314653586387159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11994218867946699872150373619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_1_1
  · norm_num [gridPoint]

theorem exp_1_2_0 : expNegUpper (2580497595454401768779 / 35442140553369651200 : ℝ) ≤ (11994166669505616515287513293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (883089 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_2_1 : expNegUpper (25762002863016351055461 / 354421405533696512000 : ℝ) ≤ (13540280707476724271981701571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882253 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_2 : rowCell 1 2 ≤ (3723989687669235095558944421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11994166669505616515287513293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13540280707476724271981701571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_2_1
  · norm_num [gridPoint]

theorem exp_1_3_0 : expNegUpper (26055294495697905132189 / 358456351603532288000 : ℝ) ≤ (5416089241393242603875059501 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (882253 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_3_1 : expNegUpper (6503227466988839267167 / 89614087900883072000 : ℝ) ≤ (3809936309566424797762865223 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_3 : rowCell 1 3 ≤ (4197322296966259903281035267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5416089241393242603875059501 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3809936309566424797762865223 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_3_1
  · norm_num [gridPoint]

theorem exp_1_4_0 : expNegUpper (87691272529955657309 / 1208380453263744000 : ℝ) ≤ (3047936370327495901226043379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_4_1 : expNegUpper (350207852344117554769 / 4833521813054976000 : ℝ) ≤ (68407544201781910877790353 / 2000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176129 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_4 : rowCell 1 4 ≤ (4716752376594602537092031813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3047936370327495901226043379 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (68407544201781910877790353 / 2000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_4_1
  · norm_num [gridPoint]

theorem exp_1_5_0 : expNegUpper (2043172902826849276799 / 28199596820036096000 : ℝ) ≤ (34203632995488682721382920941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (176129 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_5_1 : expNegUpper (1020001924189052938521 / 14099798410018048000 : ℝ) ≤ (19135860921492795481537389423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27496 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_5 : rowCell 1 5 ≤ (5284967989398156728800918849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34203632995488682721382920941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19135860921492795481537389423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_5_1
  · norm_num [gridPoint]

theorem exp_1_6_0 : expNegUpper (13408451210661791039157 / 185349109823785216000 : ℝ) ≤ (4783946203716926091640778701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (27496 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_6_1 : expNegUpper (5355260633922736635869 / 74139643929514086400 : ℝ) ≤ (21350628240425774410172461503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_6 : rowCell 1 6 ≤ (1476152807251864918817198349 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4783946203716926091640778701 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21350628240425774410172461503 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_6_1
  · norm_num [gridPoint]

theorem exp_1_7_0 : expNegUpper (1804957053669931224103 / 24988301262695116800 : ℝ) ≤ (4270109037941432109054177239 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1758239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_7_1 : expNegUpper (1126431597510099319589 / 15617688289184448000 : ℝ) ≤ (47509718812619943108534599369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878387 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_7 : rowCell 1 7 ≤ (6578253255057022013680890387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4270109037941432109054177239 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47509718812619943108534599369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_7_1
  · norm_num [gridPoint]

theorem exp_1_8_0 : expNegUpper (3416702235032980772143 / 47371707067379776000 : ℝ) ≤ (47509538042480646146072217367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (878387 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_8_1 : expNegUpper (27294225533140124602983 / 378973656539038208000 : ℝ) ≤ (52713696009416310032396690521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (438837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_8 : rowCell 1 8 ≤ (7308368271376169545705519357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47509538042480646146072217367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (52713696009416310032396690521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_8_1
  · norm_num [gridPoint]

theorem exp_1_9_0 : expNegUpper (1103787945572274490167 / 15325825297736192000 : ℝ) ≤ (13178374948646255403011194877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (438837 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_9_1 : expNegUpper (551118294812911054139 / 7662912648868096000 : ℝ) ≤ (58328833302482965434955991753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43849 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_9 : rowCell 1 9 ≤ (8097306694034339512486908781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13178374948646255403011194877 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58328833302482965434955991753 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_9_1
  · norm_num [gridPoint]

theorem exp_1_10_0 : expNegUpper (4642934679086110553617 / 64556741108921088000 : ℝ) ≤ (58328620876398639477929337033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1753961 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_10_1 : expNegUpper (9273145318365771570367 / 129113482217842176000 : ℝ) ≤ (12873928986526883714764017169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1752611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_10 : rowCell 1 10 ≤ (1789453555903575679254332257 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58328620876398639477929337033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12873928986526883714764017169 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_10_1
  · norm_num [gridPoint]

theorem exp_1_11_0 : expNegUpper (28122356178231896108789 / 391558099169403392000 : ℝ) ≤ (32184707771615385941617178871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1752611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_11_1 : expNegUpper (56169598337668114689 / 783116198338806784 : ℝ) ≤ (70849324415350253683683145771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (875649 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_11 : rowCell 1 11 ≤ (4930136001683204960989891067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32184707771615385941617178871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (70849324415350253683683145771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_11_1
  · norm_num [gridPoint]

theorem exp_1_12_0 : expNegUpper (56777905885582414689 / 791597179982070784 : ℝ) ≤ (70849077330239936715264940017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (875649 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_12_1 : expNegUpper (28352014374194427336211 / 395798589991035392000 : ℝ) ≤ (77779556272552212574975046243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1750021 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_12 : rowCell 1 12 ≤ (10838133495853606034815927749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (70849077330239936715264940017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (77779556272552212574975046243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_12_1
  · norm_num [gridPoint]

theorem exp_1_13_0 : expNegUpper (9552469453511081252633 / 133353973039474176000 : ℝ) ≤ (38889645392141412087388432441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (875011 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_13_1 : expNegUpper (4770181927252845235883 / 66676986519737088000 : ℝ) ≤ (85170331450014745928233234637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1748781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_13 : rowCell 1 13 ≤ (11882432853376204938634635881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (38889645392141412087388432441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (85170331450014745928233234637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_13_1
  · norm_num [gridPoint]

theorem exp_1_14_0 : expNegUpper (578554648475933041561 / 8086961731031296000 : ℝ) ≤ (42585023440674114618087734641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1748781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_14_1 : expNegUpper (1155681629165625452433 / 16173923462062592000 : ℝ) ≤ (93029768675570567777431145589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69903 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_14 : rowCell 1 14 ≤ (12994490651807308097463886269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42585023440674114618087734641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93029768675570567777431145589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_14_1
  · norm_num [gridPoint]

theorem exp_1_15_0 : expNegUpper (29199935124920079034017 / 408657092290462208000 : ℝ) ≤ (93029464384736127173427091811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69903 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_15_1 : expNegUpper (1822804491462735546991 / 25541068268153888000 : ℝ) ≤ (101363944016523509230410302057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436601 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_15 : rowCell 1 15 ≤ (7087670995473856596636202167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93029464384736127173427091811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (101363944016523509230410302057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_15_1
  · norm_num [gridPoint]

theorem exp_1_16_0 : expNegUpper (614042217838378569893 / 8603936173648224000 : ℝ) ≤ (101363619402393441448137256549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436601 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_16_1 : expNegUpper (1962639663909674364497 / 27532595755674316800 : ℝ) ≤ (110176730864306575076708221551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1745267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_16 : rowCell 1 16 ≤ (3856428099307801985821957201 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (101363619402393441448137256549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (110176730864306575076708221551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_16_1
  · norm_num [gridPoint]

theorem exp_1_17_0 : expNegUpper (5950003282020315153931 / 83468723737104486400 : ℝ) ≤ (344301204285763516410772593 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1745267 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_17_1 : expNegUpper (14858110003601661593343 / 208671809342761216000 : ℝ) ≤ (119469652510381908500932514897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1744163 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_17 : rowCell 1 17 ≤ (3349199080990985683696083577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (344301204285763516410772593 / 3125000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (119469652510381908500932514897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_17_1
  · norm_num [gridPoint]

theorem exp_1_18_0 : expNegUpper (1154919806878343807979 / 16220043820834048000 : ℝ) ≤ (119469285633912246325879506761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436041 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_18_1 : expNegUpper (2307289000109002972201 / 32440087641668096000 : ℝ) ≤ (64620874690126023934320415539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (435773 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_18 : rowCell 1 18 ≤ (725449284982135234835899537 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (119469285633912246325879506761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (64620874690126023934320415539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_18_1
  · norm_num [gridPoint]

theorem exp_1_19_0 : expNegUpper (13035583722488992601 / 183278063786496000 : ℝ) ≤ (129241360670504501263148241107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1743093 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_19_1 : expNegUpper (3255399562755366511 / 45819515946624000 : ℝ) ≤ (139489462863427945641021576881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (871027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_19 : rowCell 1 19 ≤ (19596093089943622795684828593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (129241360670504501263148241107 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (139489462863427945641021576881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_19_1
  · norm_num [gridPoint]

theorem exp_1_20_0 : expNegUpper (7647369482572532217083 / 107636173892819072000 : ℝ) ≤ (34872262982576627370315864437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (871027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_20_1 : expNegUpper (30557606796165579656811 / 430544695571276288000 : ℝ) ≤ (15020653751805036859064802923 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_20 : rowCell 1 20 ≤ (5281215663988832139284107091 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34872262982576627370315864437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15020653751805036859064802923 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_20_1
  · norm_num [gridPoint]

theorem exp_1_21_0 : expNegUpper (30873162297685248949539 / 434990731144704512000 : ℝ) ≤ (150206104035084993834717032343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741047 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_21_1 : expNegUpper (3084193958137769868121 / 43499073114470451200 : ℝ) ≤ (80691971620951127178329920113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1740071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_21 : rowCell 1 21 ≤ (2840178273952626319543249811 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (150206104035084993834717032343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80691971620951127178329920113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_21_1
  · norm_num [gridPoint]

theorem exp_1_22_0 : expNegUpper (1038626508310363825667 / 14648653500796262400 : ℝ) ≤ (6455339477997627136817672649 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1740071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_22_1 : expNegUpper (10376074760533304118187 / 146486535007962624000 : ℝ) ≤ (173009818789588042824083982621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13913 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_22 : rowCell 1 22 ≤ (24384260286012059710986314381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6455339477997627136817672649 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (173009818789588042824083982621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_22_1
  · norm_num [gridPoint]

theorem exp_1_23_0 : expNegUpper (31446386777505773058809 / 443951317208826368000 : ℝ) ≤ (173009339500090096774595111779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13913 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_23_1 : expNegUpper (3927058861146358425741 / 55493914651103296000 : ℝ) ≤ (23133679722741591215923164413 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173821 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_23 : rowCell 1 23 ≤ (6527856537701642206476899529 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (173009339500090096774595111779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23133679722741591215923164413 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_23_1
  · norm_num [gridPoint]

theorem exp_1_24_0 : expNegUpper (6347189374921694109 / 89693173539904000 : ℝ) ≤ (185068935379833295621120041301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (173821 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_24_1 : expNegUpper (50730703034286736903 / 717545388319232000 : ℝ) ≤ (7901807924070978690620297013 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_24 : rowCell 1 24 ≤ (27900566368364387951667343321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (185068935379833295621120041301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7901807924070978690620297013 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_24_1
  · norm_num [gridPoint]

theorem exp_1_25_0 : expNegUpper (10675828510985884652549 / 151001085498656256000 : ℝ) ≤ (98772336273942848628618335359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_25_1 : expNegUpper (5333148299285598093161 / 75500542749328128000 : ℝ) ≤ (210416635304187184885111867359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_25 : rowCell 1 25 ≤ (29748905096310677912550105163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (98772336273942848628618335359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (210416635304187184885111867359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_25_1
  · norm_num [gridPoint]

theorem exp_1_26_0 : expNegUpper (16160506372445985012907 / 228781741799086336000 : ℝ) ≤ (210416086637115364960147097583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (434117 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_26_1 : expNegUpper (6458616415872529623753 / 91512696719634534400 : ℝ) ≤ (223660460392883811519449632303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43391 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_26 : rowCell 1 26 ≤ (31653251800075262213777311931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (210416086637115364960147097583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (223660460392883811519449632303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_26_1
  · norm_num [gridPoint]

theorem exp_1_27_0 : expNegUpper (6523307700550013095713 / 92429309801226342400 : ℝ) ≤ (111829944365220642747584560959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43391 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_27_1 : expNegUpper (8147319059928758993209 / 115536637251532928000 : ℝ) ≤ (237250622032357823582639573969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43371 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_27 : rowCell 1 27 ≤ (16805004272055162243139186099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (111829944365220642747584560959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (237250622032357823582639573969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_27_1
  · norm_num [gridPoint]

theorem exp_1_28_0 : expNegUpper (2742839399905882253747 / 38896037726653824000 : ℝ) ≤ (47450005514491122724018345619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (43371 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_28_1 : expNegUpper (10962494089703132950081 / 155584150906615296000 : ℝ) ≤ (251158392981512700634351823957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_28 : rowCell 1 28 ≤ (35615180831235710931341361793 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47450005514491122724018345619 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (251158392981512700634351823957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_28_1
  · norm_num [gridPoint]

theorem exp_1_29_0 : expNegUpper (1328545025023687258163 / 18855247789572608000 : ℝ) ≤ (50231555200504958817535961987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433517 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_29_1 : expNegUpper (663754203197687669601 / 9427623894786304000 : ℝ) ≤ (265352480253366864710956973043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_29 : rowCell 1 29 ≤ (7532878387672594932451759223 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50231555200504958817535961987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (265352480253366864710956973043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_29_1
  · norm_num [gridPoint]

theorem exp_1_30_0 : expNegUpper (16757603487626747717481 / 238016387532269824000 : ℝ) ≤ (132675920556981254589732143127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (433331 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_30_1 : expNegUpper (33489969904378636591321 / 476032775064539648000 : ℝ) ≤ (139899579115529772378051032947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866303 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_30 : rowCell 1 30 ≤ (7950580131267996443246616227 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (132675920556981254589732143127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (139899579115529772378051032947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_30_1
  · norm_num [gridPoint]

theorem exp_1_31_0 : expNegUpper (867149406158799377351 / 12325825479372288000 : ℝ) ≤ (279798497369505230673173117763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866303 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_31_1 : expNegUpper (5415748637008141813 / 77036409246076800 : ℝ) ≤ (147231211853396932862898819749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346383 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_31 : rowCell 1 31 ≤ (4187562230243000959688236857 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (279798497369505230673173117763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (147231211853396932862898819749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_31_1
  · norm_num [gridPoint]

theorem sum_1_0_2 : blockSum (rowCell 1) 0 2 ≤ (6198819639269498066961298443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_0) (by simpa only [blockSum_one] using cell_1_1) (by norm_num)

theorem sum_1_2_2 : blockSum (rowCell 1) 2 2 ≤ (990163998079436874854997461 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_2) (by simpa only [blockSum_one] using cell_1_3) (by norm_num)

theorem sum_1_0_4 : blockSum (rowCell 1) 0 4 ≤ (14120131623904993065801278131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_0_2 sum_1_2_2 (by norm_num)

theorem sum_1_4_2 : blockSum (rowCell 1) 4 2 ≤ (5000860182996379632946475331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_4) (by simpa only [blockSum_one] using cell_1_5) (by norm_num)

theorem sum_1_6_2 : blockSum (rowCell 1) 6 2 ≤ (12482864484064481688949683783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_6) (by simpa only [blockSum_one] using cell_1_7) (by norm_num)

theorem sum_1_4_4 : blockSum (rowCell 1) 4 4 ≤ (4496916970011448190968526889 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_4_2 sum_1_6_2 (by norm_num)

theorem sum_1_0_8 : blockSum (rowCell 1) 0 8 ≤ (285974347452829953286280567 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_0_4 sum_1_4_4 (by norm_num)

theorem sum_1_8_2 : blockSum (rowCell 1) 8 2 ≤ (7702837482705254529096214069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_8) (by simpa only [blockSum_one] using cell_1_9) (by norm_num)

theorem sum_1_10_2 : blockSum (rowCell 1) 10 2 ≤ (18807539782884288318251443419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_10) (by simpa only [blockSum_one] using cell_1_11) (by norm_num)

theorem sum_1_8_4 : blockSum (rowCell 1) 8 4 ≤ (34213214748294797376443871557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_8_2 sum_1_10_2 (by norm_num)

theorem sum_1_12_2 : blockSum (rowCell 1) 12 2 ≤ (2272056634922981097345056363 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_12) (by simpa only [blockSum_one] using cell_1_13) (by norm_num)

theorem sum_1_14_2 : blockSum (rowCell 1) 14 2 ≤ (27169832642755021290736290603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_14) (by simpa only [blockSum_one] using cell_1_15) (by norm_num)

theorem sum_1_12_4 : blockSum (rowCell 1) 12 4 ≤ (49890398991984832264186854233 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_12_2 sum_1_14_2 (by norm_num)

theorem sum_1_8_8 : blockSum (rowCell 1) 8 8 ≤ (8410361374027962964063072579 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_8_4 sum_1_12_4 (by norm_num)

theorem sum_1_0_16 : blockSum (rowCell 1) 0 16 ≤ (60354165107120931830637319183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_0_8 sum_1_8_8 (by norm_num)

theorem sum_1_16_2 : blockSum (rowCell 1) 16 2 ≤ (32171707802186136361768246689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_16) (by simpa only [blockSum_one] using cell_1_17) (by norm_num)

theorem sum_1_18_2 : blockSum (rowCell 1) 18 2 ≤ (18866162607248501833291158509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_18) (by simpa only [blockSum_one] using cell_1_19) (by norm_num)

theorem sum_1_16_4 : blockSum (rowCell 1) 16 4 ≤ (69904033016683140028350563707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_16_2 sum_1_18_2 (by norm_num)

theorem sum_1_20_2 : blockSum (rowCell 1) 20 2 ≤ (10961572211894084778370606713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_20) (by simpa only [blockSum_one] using cell_1_21) (by norm_num)

theorem sum_1_22_2 : blockSum (rowCell 1) 22 2 ≤ (50495686436818628536893912497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_22) (by simpa only [blockSum_one] using cell_1_23) (by norm_num)

theorem sum_1_20_4 : blockSum (rowCell 1) 20 4 ≤ (94341975284394967650376339349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_20_2 sum_1_22_2 (by norm_num)

theorem sum_1_16_8 : blockSum (rowCell 1) 16 8 ≤ (10265375518817381729920431441 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_16_4 sum_1_20_4 (by norm_num)

theorem sum_1_24_2 : blockSum (rowCell 1) 24 2 ≤ (14412367866168766466054362121 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_24) (by simpa only [blockSum_one] using cell_1_25) (by norm_num)

theorem sum_1_26_2 : blockSum (rowCell 1) 26 2 ≤ (65263260344185586700055684129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_26) (by simpa only [blockSum_one] using cell_1_27) (by norm_num)

theorem sum_1_24_4 : blockSum (rowCell 1) 24 4 ≤ (122912731808860652564273132613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_24_2 sum_1_26_2 (by norm_num)

theorem sum_1_28_2 : blockSum (rowCell 1) 28 2 ≤ (18319893192399671398400039477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_28) (by simpa only [blockSum_one] using cell_1_29) (by norm_num)

theorem sum_1_30_2 : blockSum (rowCell 1) 30 2 ≤ (16325704591753998362623089941 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_30) (by simpa only [blockSum_one] using cell_1_31) (by norm_num)

theorem sum_1_28_4 : blockSum (rowCell 1) 28 4 ≤ (154908095728368677406715607613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_28_2 sum_1_30_2 (by norm_num)

theorem sum_1_24_8 : blockSum (rowCell 1) 24 8 ≤ (138910413768614664985494370113 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_24_4 sum_1_28_4 (by norm_num)

theorem sum_1_16_16 : blockSum (rowCell 1) 16 16 ≤ (221033417919153718824857821641 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_16_8 sum_1_24_8 (by norm_num)

theorem sum_1_0_32 : blockSum (rowCell 1) 0 32 ≤ (35173447878284331331936892603 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_0_16 sum_1_16_16 (by norm_num)

#print axioms sum_1_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
