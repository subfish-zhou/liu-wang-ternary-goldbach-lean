import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_0_0 : expNegUpper (56057474713525940881 / 676601617795489000 : ℝ) ≤ (4173829215762107383661 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (477583 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_0_1 : expNegUpper (28637869068379016690191 / 346420028311290368000 : ℝ) ≤ (626794353324601301557719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476899 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_0 : rowCell 5 0 ≤ (16750265884447821063337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4173829215762107383661 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (626794353324601301557719 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_0_1
  · norm_num [gridPoint]

theorem exp_5_1_0 : expNegUpper (28967656085412308130439 / 350409297769615872000 : ℝ) ≤ (1253581980126445228153479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (476899 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_1_1 : expNegUpper (2890467990269206383899 / 35040929776961587200 : ℝ) ≤ (1500392615380367541161259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47623 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_1 : rowCell 5 1 ≤ (200822301778407437790529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1253581980126445228153479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1500392615380367541161259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_1_1
  · norm_num [gridPoint]

theorem exp_5_2_0 : expNegUpper (2923563385495694568779 / 35442140553369651200 : ℝ) ≤ (60015389852320609489369 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47623 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_2_1 : expNegUpper (29173242805242271055461 / 354421405533696512000 : ℝ) ≤ (223647613153955512336803 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_2 : rowCell 5 2 ≤ (119939041389706006969301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (60015389852320609489369 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (223647613153955512336803 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_2_1
  · norm_num [gridPoint]

theorem exp_5_3_0 : expNegUpper (29505370354297841132189 / 358456351603532288000 : ℝ) ≤ (447292933053432416953697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_3_1 : expNegUpper (7360891942092071267167 / 89614087900883072000 : ℝ) ≤ (2125837698073386149992093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_3 : rowCell 5 3 ≤ (35685750630977688626887 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (447292933053432416953697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2125837698073386149992093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_3_1
  · norm_num [gridPoint]

theorem exp_5_4_0 : expNegUpper (297768755757736411927 / 3625141359791232000 : ℝ) ≤ (265728380293211949600359 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1899741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_4_1 : expNegUpper (1188626591376350104307 / 14500565439164928000 : ℝ) ≤ (503371799275671511911841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_4 : rowCell 5 4 ≤ (338548837106995872303431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (265728380293211949600359 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (503371799275671511911841 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_4_1
  · norm_num [gridPoint]

theorem exp_5_5_0 : expNegUpper (30050159511722992598387 / 366594758660469248000 : ℝ) ≤ (2516846660730941535836543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1897237 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_5_1 : expNegUpper (14994771922851160200773 / 183297379330234624000 : ℝ) ≤ (1484692220581194791311341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (473697 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_5 : rowCell 5 5 ≤ (100015225246454328111931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2516846660730941535836543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1484692220581194791311341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_5_1
  · norm_num [gridPoint]

theorem exp_5_6_0 : expNegUpper (15162616077242271039157 / 185349109823785216000 : ℝ) ≤ (371171276112424779928879 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (473697 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_6_1 : expNegUpper (6053042988917527035869 / 74139643929514086400 : ℝ) ≤ (218201639555310568292749 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_6 : rowCell 5 6 ≤ (7361132765266120804693 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (371171276112424779928879 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (218201639555310568292749 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_6_1
  · norm_num [gridPoint]

theorem exp_5_7_0 : expNegUpper (6120420699279387272309 / 74964903788085350400 : ℝ) ≤ (1745604933418762555170933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_7_1 : expNegUpper (3817836009175417958767 / 46853064867553344000 : ℝ) ≤ (4090894490572426644936713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_7 : rowCell 5 7 ≤ (110578772357843458499689 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1745604933418762555170933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4090894490572426644936713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_7_1
  · norm_num [gridPoint]

theorem exp_5_8_0 : expNegUpper (3860097941224852772143 / 47371707067379776000 : ℝ) ≤ (31959966657664481192693 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_8_1 : expNegUpper (30821973224488092602983 / 378973656539038208000 : ℝ) ≤ (2388809149562886495179109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_8 : rowCell 5 8 ≤ (8083731906881250583263 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31959966657664481192693 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2388809149562886495179109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_8_1
  · norm_num [gridPoint]

theorem exp_5_9_0 : expNegUpper (26520240210237315961 / 326081389313536000 : ℝ) ≤ (2388798433804754796754889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_9_1 : expNegUpper (13235353357523629237 / 163040694656768000 : ℝ) ≤ (5561361679980351533215939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942761 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_9 : rowCell 5 9 ≤ (94240768274790346703337 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2388798433804754796754889 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5561361679980351533215939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_9_1
  · norm_num [gridPoint]

theorem exp_5_10_0 : expNegUpper (15721804820212827660851 / 193670223326763264000 : ℝ) ≤ (5561337271610082188002807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942761 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_10_1 : expNegUpper (31386019562819298711101 / 387340446653526528000 : ℝ) ≤ (80660421464907670818113 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1883333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_10 : rowCell 5 10 ≤ (175216828497048066811153 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5561337271610082188002807 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80660421464907670818113 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_10_1
  · norm_num [gridPoint]

theorem exp_5_11_0 : expNegUpper (31727775702327896108789 / 391558099169403392000 : ℝ) ≤ (6452806004686309624888731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1883333 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_11_1 : expNegUpper (63341601469486098689 / 783116198338806784 : ℝ) ≤ (7463492080677341581706891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881193 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_11 : rowCell 5 11 ≤ (507394479654389257445167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6452806004686309624888731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7463492080677341581706891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_11_1
  · norm_num [gridPoint]

theorem exp_5_12_0 : expNegUpper (64027580850148430689 / 791597179982070784 : ℝ) ≤ (3731730356367408470800969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881193 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_12_1 : expNegUpper (31957433898290427336211 / 395798589991035392000 : ℝ) ≤ (537846200721772020814687 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939551 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_12 : rowCell 5 12 ≤ (1171765911470848176666421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3731730356367408470800969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (537846200721772020814687 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_12_1
  · norm_num [gridPoint]

theorem exp_5_13_0 : expNegUpper (32301663801003259757899 / 400061919118422528000 : ℝ) ≤ (4302751906271389725644323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (939551 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_13_1 : expNegUpper (16122964522900039707649 / 200030959559211264000 : ℝ) ≤ (4945955235971190694780427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_13 : rowCell 5 13 ≤ (1348848068395304145651439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4302751906271389725644323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4945955235971190694780427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_13_1
  · norm_num [gridPoint]

theorem exp_5_14_0 : expNegUpper (651828116449073521561 / 8086961731031296000 : ℝ) ≤ (989187064178517122717789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_14_1 : expNegUpper (1301451846784426092433 / 16173923462062592000 : ℝ) ≤ (113362536136907861349829 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93753 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_14 : rowCell 5 14 ≤ (193496736606524073753651 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (989187064178517122717789 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (113362536136907861349829 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_14_1
  · norm_num [gridPoint]

theorem exp_5_15_0 : expNegUpper (32883026481764111034017 / 408657092290462208000 : ℝ) ≤ (2834052231971378636438839 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (93753 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_15_1 : expNegUpper (2051784078878799546991 / 25541068268153888000 : ℝ) ≤ (3238224746707984666890219 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (468277 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_15 : rowCell 5 15 ≤ (1771183571386588817276891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2834052231971378636438839 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3238224746707984666890219 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_15_1
  · norm_num [gridPoint]

theorem exp_5_16_0 : expNegUpper (2073533485704575709679 / 25811808520944672000 : ℝ) ≤ (2590569799346357862346611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (468277 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_16_1 : expNegUpper (6624537263097829493491 / 82597787267022950400 : ℝ) ≤ (1844602498752603345125223 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_16 : rowCell 5 16 ≤ (126288372369983190598583 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2590569799346357862346611 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1844602498752603345125223 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_16_1
  · norm_num [gridPoint]

theorem exp_5_17_0 : expNegUpper (6694388736663924753931 / 83468723737104486400 : ℝ) ≤ (14756764223302529798349643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_17_1 : expNegUpper (16709364661117181593343 / 208671809342761216000 : ℝ) ≤ (16763583359880599451544979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (934669 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_17 : rowCell 5 17 ≤ (1149246032413997775497501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14756764223302529798349643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16763583359880599451544979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_17_1
  · norm_num [gridPoint]

theorem exp_5_18_0 : expNegUpper (16884630105120997503727 / 210860569670842624000 : ℝ) ≤ (16763521321246082587807813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (934669 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_18_1 : expNegUpper (33716684274635086638613 / 421721139341685248000 : ℝ) ≤ (18989289004436555974650657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_18 : rowCell 5 18 ≤ (325890881326788123058757 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16763521321246082587807813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18989289004436555974650657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_18_1
  · norm_num [gridPoint]

theorem exp_5_19_0 : expNegUpper (43959348831456737803 / 549834191359488000 : ℝ) ≤ (4747305044137876562976469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867519 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_19_1 : expNegUpper (10973084246783859533 / 137458547839872000 : ℝ) ≤ (21450499205857218769288071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_19 : rowCell 5 19 ≤ (2948900669925626861384349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4747305044137876562976469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21450499205857218769288071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_19_1
  · norm_num [gridPoint]

theorem exp_5_20_0 : expNegUpper (8592414769517300217083 / 107636173892819072000 : ℝ) ≤ (10725211525266750183750791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865741 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_20_1 : expNegUpper (34318369985757643656811 / 430544695571276288000 : ℝ) ≤ (24164157148389683899747771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_20 : rowCell 5 20 ≤ (831564042488719016704047 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10725211525266750183750791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24164157148389683899747771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_20_1
  · norm_num [gridPoint]

theorem exp_5_21_0 : expNegUpper (34672761403651328949539 / 434990731144704512000 : ℝ) ≤ (24164073108016094748019973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932003 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_21_1 : expNegUpper (3462212072915677068121 / 43499073114470451200 : ℝ) ≤ (27147494866935169131971649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_21 : rowCell 5 21 ≤ (935421409242574664351283 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24164073108016094748019973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27147494866935169131971649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_21_1
  · norm_num [gridPoint]

theorem exp_5_22_0 : expNegUpper (3497781231346400277001 / 43945960502388787200 : ℝ) ≤ (13573701183079188729715069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_22_1 : expNegUpper (34927823387565992354561 / 439459605023887872000 : ℝ) ≤ (7604482714559126767390729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860657 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_22 : rowCell 5 22 ≤ (4197715817576943772133243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13573701183079188729715069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7604482714559126767390729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_22_1
  · norm_num [gridPoint]

theorem exp_5_23_0 : expNegUpper (35284821799845869058809 / 443951317208826368000 : ℝ) ≤ (30417829305891222367226891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860657 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_23_1 : expNegUpper (4404435994165494425741 / 55493914651103296000 : ℝ) ≤ (16996478873999085532763033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929521 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_23 : rowCell 5 23 ≤ (2348446230518054148934129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30417829305891222367226891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16996478873999085532763033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_23_1
  · norm_num [gridPoint]

theorem exp_5_24_0 : expNegUpper (7118759971027114909 / 89693173539904000 : ℝ) ≤ (33992846539282709975636659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929521 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_24_1 : expNegUpper (56872199070030890503 / 717545388319232000 : ℝ) ≤ (18945010280554859297376539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1857467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_24 : rowCell 5 24 ≤ (1310440812806006600043841 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33992846539282709975636659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18945010280554859297376539 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_24_1
  · norm_num [gridPoint]

theorem exp_5_25_0 : expNegUpper (35904756471671765957647 / 453003256495968768000 : ℝ) ≤ (1515595963200006620406789 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1857467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_25_1 : expNegUpper (17928371388120346279483 / 226501628247984384000 : ℝ) ≤ (263289914350241839496471 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855929 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_25 : rowCell 5 25 ≤ (5834859419252146193687931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1515595963200006620406789 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (263289914350241839496471 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_25_1
  · norm_num [gridPoint]

theorem exp_5_26_0 : expNegUpper (18108850820896545012907 / 228781741799086336000 : ℝ) ≤ (4212625391793187157702901 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855929 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_26_1 : expNegUpper (7234070603615352023753 / 91512696719634534400 : ℝ) ≤ (23359502827926882749079231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185443 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_26 : rowCell 5 26 ≤ (6478676150033346978555981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4212625391793187157702901 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23359502827926882749079231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_26_1
  · norm_num [gridPoint]

theorem exp_5_27_0 : expNegUpper (7306529071567638695713 / 92429309801226342400 : ℝ) ≤ (46718861750426262923258251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185443 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_27_1 : expNegUpper (9121491284154038993209 / 115536637251532928000 : ℝ) ≤ (51684367934648378217387091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_27 : rowCell 5 27 ≤ (7175651917787313016223759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (46718861750426262923258251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51684367934648378217387091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_27_1
  · norm_num [gridPoint]

theorem exp_5_28_0 : expNegUpper (9212399403036430761241 / 116688113179961472000 : ℝ) ≤ (25842105934457995437106263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_28_1 : expNegUpper (36803589124197526850243 / 466752452719845888000 : ℝ) ≤ (57038350196786122314883301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_28 : rowCell 5 28 ≤ (7928146906257853997991187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (25842105934457995437106263 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (57038350196786122314883301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_28_1
  · norm_num [gridPoint]

theorem exp_5_29_0 : expNegUpper (1486742735882173018163 / 18855247789572608000 : ℝ) ≤ (14259545334586313197793247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851541 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_29_1 : expNegUpper (742464699463190389601 / 9427623894786304000 : ℝ) ≤ (62796062014870644293328201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37003 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_29 : rowCell 5 29 ≤ (2184605172223628967577341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14259545334586313197793247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62796062014870644293328201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_29_1
  · norm_num [gridPoint]

theorem exp_5_30_0 : expNegUpper (18744783852451323717481 / 238016387532269824000 : ℝ) ≤ (12559175947060116946248967 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (37003 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_30_1 : expNegUpper (37444912675840780591321 / 476032775064539648000 : ℝ) ≤ (2155365223383067781205171 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369759 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_30 : rowCell 5 30 ≤ (2402152340518119067323893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12559175947060116946248967 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2155365223383067781205171 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_30_1
  · norm_num [gridPoint]

theorem exp_5_31_0 : expNegUpper (37812605528029335716689 / 480707193695519232000 : ℝ) ≤ (17242872706665182377093873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (369759 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_31_1 : expNegUpper (236053951403624730707 / 3004419960596995200 : ℝ) ≤ (37789161822522270473280753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923737 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_31 : rowCell 5 31 ≤ (10540702340250687744277931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17242872706665182377093873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37789161822522270473280753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_31_1
  · norm_num [gridPoint]

theorem sum_5_0_2 : blockSum (rowCell 5) 0 2 ≤ (368324960622885648423899 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_0) (by simpa only [blockSum_one] using cell_5_1) (by norm_num)

theorem sum_5_2_2 : blockSum (rowCell 5) 2 2 ≤ (262682043913616761476849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_2) (by simpa only [blockSum_one] using cell_5_3) (by norm_num)

theorem sum_5_0_4 : blockSum (rowCell 5) 0 4 ≤ (893689048450119171377597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_0_2 sum_5_2_2 (by norm_num)

theorem sum_5_4_2 : blockSum (rowCell 5) 4 2 ≤ (147721947618562636950231 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_4) (by simpa only [blockSum_one] using cell_5_5) (by norm_num)

theorem sum_5_6_2 : blockSum (rowCell 5) 6 2 ≤ (1024006358766249023998797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_6) (by simpa only [blockSum_one] using cell_5_7) (by norm_num)

theorem sum_5_4_4 : blockSum (rowCell 5) 4 4 ≤ (13770438256711423505859 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_4_2 sum_5_6_2 (by norm_num)

theorem sum_5_0_8 : blockSum (rowCell 5) 0 8 ≤ (2656305145309181380127549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_0_4 sum_5_4_4 (by norm_num)

theorem sum_5_8_2 : blockSum (rowCell 5) 8 2 ≤ (175078087343602852535967 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_8) (by simpa only [blockSum_one] using cell_5_9) (by norm_num)

theorem sum_5_10_2 : blockSum (rowCell 5) 10 2 ≤ (1890873101794018848946099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_10) (by simpa only [blockSum_one] using cell_5_11) (by norm_num)

theorem sum_5_8_4 : blockSum (rowCell 5) 8 4 ≤ (658299560108568333846767 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_8_2 sum_5_10_2 (by norm_num)

theorem sum_5_12_2 : blockSum (rowCell 5) 12 2 ≤ (126030698993307616115893 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_12) (by simpa only [blockSum_one] using cell_5_13) (by norm_num)

theorem sum_5_14_2 : blockSum (rowCell 5) 14 2 ≤ (3319157464238781407306099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_14) (by simpa only [blockSum_one] using cell_5_15) (by norm_num)

theorem sum_5_12_4 : blockSum (rowCell 5) 12 4 ≤ (5839771444104933729623959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_12_2 sum_5_14_2 (by norm_num)

theorem sum_5_8_8 : blockSum (rowCell 5) 8 8 ≤ (4565634622323887699428897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_8_4 sum_5_12_4 (by norm_num)

theorem sum_5_0_16 : blockSum (rowCell 5) 0 16 ≤ (11787574389956956778985343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_0_8 sum_5_8_8 (by norm_num)

theorem sum_5_16_2 : blockSum (rowCell 5) 16 2 ≤ (431910602274772660057233 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_16) (by simpa only [blockSum_one] using cell_5_17) (by norm_num)

theorem sum_5_18_2 : blockSum (rowCell 5) 18 2 ≤ (1111205544107986369170881 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_18) (by simpa only [blockSum_one] using cell_5_19) (by norm_num)

theorem sum_5_16_4 : blockSum (rowCell 5) 16 4 ≤ (1975026748657531689285347 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_16_2 sum_5_18_2 (by norm_num)

theorem sum_5_20_2 : blockSum (rowCell 5) 20 2 ≤ (176698545173129368105533 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_20) (by simpa only [blockSum_one] using cell_5_21) (by norm_num)

theorem sum_5_22_2 : blockSum (rowCell 5) 22 2 ≤ (8894608278613052070001501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_22) (by simpa only [blockSum_one] using cell_5_23) (by norm_num)

theorem sum_5_20_4 : blockSum (rowCell 5) 20 4 ≤ (15962550085538226794222821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_20_2 sum_5_22_2 (by norm_num)

theorem sum_5_16_8 : blockSum (rowCell 5) 16 8 ≤ (6459420957206471310162389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_16_4 sum_5_20_4 (by norm_num)

theorem sum_5_24_2 : blockSum (rowCell 5) 24 2 ≤ (2215324534095234518772659 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_24) (by simpa only [blockSum_one] using cell_5_25) (by norm_num)

theorem sum_5_26_2 : blockSum (rowCell 5) 26 2 ≤ (682716403391032999738987 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_26) (by simpa only [blockSum_one] using cell_5_27) (by norm_num)

theorem sum_5_24_4 : blockSum (rowCell 5) 24 4 ≤ (4946190147659366517728607 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_24_2 sum_5_26_2 (by norm_num)

theorem sum_5_28_2 : blockSum (rowCell 5) 28 2 ≤ (16666567595152369868300551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_28) (by simpa only [blockSum_one] using cell_5_29) (by norm_num)

theorem sum_5_30_2 : blockSum (rowCell 5) 30 2 ≤ (20149311702323164013573503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_30) (by simpa only [blockSum_one] using cell_5_31) (by norm_num)

theorem sum_5_28_4 : blockSum (rowCell 5) 28 4 ≤ (18407939648737766940937027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_28_2 sum_5_30_2 (by norm_num)

theorem sum_5_24_8 : blockSum (rowCell 5) 24 8 ≤ (61546830035772366470517089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_24_4 sum_5_28_4 (by norm_num)

theorem sum_5_16_16 : blockSum (rowCell 5) 16 16 ≤ (17476902772919650342233329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_16_8 sum_5_24_8 (by norm_num)

theorem sum_5_0_32 : blockSum (rowCell 5) 0 32 ≤ (24793022063638802122537997 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_0_16 sum_5_16_16 (by norm_num)

#print axioms sum_5_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
