import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_32_0 : expNegUpper (203872165440569881427 / 3033777816451587200 : ℝ) ≤ (3269536526092751772879308267911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (422617 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_32_1 : expNegUpper (32602957915940975174511 / 485404450632253952000 : ℝ) ≤ (6766406352805944979926956382437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1690017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_32 : rowCell 0 32 ≤ (30320234761050917140547711651 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3269536526092751772879308267911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6766406352805944979926956382437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_32_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_32_1
  · norm_num [gridPoint]

theorem exp_0_33_0 : expNegUpper (32919991608683406098919 / 490124545874743808000 : ℝ) ≤ (6766392163296540670820652308877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1690017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_33_1 : expNegUpper (16452045720652393052279 / 245062272937371904000 : ℝ) ≤ (6989500573764263959856996835797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_33 : rowCell 0 33 ≤ (1003092057196354826735674550081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6766392163296540670820652308877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6989500573764263959856996835797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_33_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_33_1
  · norm_num [gridPoint]

theorem exp_0_34_0 : expNegUpper (73827789420377639239 / 1099705509828864000 : ℝ) ≤ (6989486196697236600233689406071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_34_1 : expNegUpper (147587985732188677477 / 2199411019657728000 : ℝ) ≤ (3603812220758293397041516308201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_34 : rowCell 0 34 ≤ (1035266062955141022145531201309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6989486196697236600233689406071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3603812220758293397041516308201 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_34_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_34_1
  · norm_num [gridPoint]

theorem exp_0_35_0 : expNegUpper (33527097354289422433277 / 499633251276988928000 : ℝ) ≤ (7207609897933050587228703910879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1689183 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_35_1 : expNegUpper (8378145988398155221719 / 124908312819247232000 : ℝ) ≤ (7420047852182239866302336415531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2111 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_35 : rowCell 0 35 ≤ (8333296446677084758419924257 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7207609897933050587228703910879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7420047852182239866302336415531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_35_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_35_1
  · norm_num [gridPoint]

theorem exp_0_36_0 : expNegUpper (8458444486595126788791 / 126105465359186048000 : ℝ) ≤ (3710016581780891253045112032163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2111 / 1250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_36_1 : expNegUpper (1352798517007757527891 / 20176874457469767680 : ℝ) ≤ (3813030112118388610377576441677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_36 : rowCell 0 36 ≤ (1097174647812799075550069474669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3710016581780891253045112032163 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3813030112118388610377576441677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_36_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_36_1
  · norm_num [gridPoint]

theorem exp_0_37_0 : expNegUpper (151744697812363726899 / 2263259155121131520 : ℝ) ≤ (7626045412394752356111382936123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_37_1 : expNegUpper (1896080205382502838477 / 28290739439014144000 : ℝ) ≤ (7824974695619717938405746682719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_37 : rowCell 0 37 ≤ (28167556701307336703171108051 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7626045412394752356111382936123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7824974695619717938405746682719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_37_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_37_1
  · norm_num [gridPoint]

theorem exp_0_38_0 : expNegUpper (17226722265416031676837 / 257033798336760064000 : ℝ) ≤ (7824959782604493743581079395219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1688099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_38_1 : expNegUpper (34441036261004606301873 / 514067596673520128000 : ℝ) ≤ (2004033028008041995808642344063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_38 : rowCell 0 38 ≤ (1155146653187904460745167294351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7824959782604493743581079395219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2004033028008041995808642344063 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_38_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_38_1
  · norm_num [gridPoint]

theorem exp_0_39_0 : expNegUpper (1390658020314793131537 / 20756988870021632000 : ℝ) ≤ (1002014640002888344301554522217 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687781 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_39_1 : expNegUpper (173773753049456252771 / 2594623608752704000 : ℝ) ≤ (8198904774685581935295664416497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_39 : rowCell 0 39 ≤ (591206982372945553295504677477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1002014640002888344301554522217 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8198904774685581935295664416497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_39_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_39_1
  · norm_num [gridPoint]

theorem exp_0_40_0 : expNegUpper (487244235156024723411 / 7275065071296064000 : ℝ) ≤ (1639777945178498379689055356051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421871 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_40_1 : expNegUpper (3896732970653736730959 / 58200520570368512000 : ℝ) ≤ (8372699918983451445259386489631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687207 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_40 : rowCell 0 40 ≤ (1208415205441925356853291905299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1639777945178498379689055356051 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8372699918983451445259386489631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_40_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_40_1
  · norm_num [gridPoint]

theorem exp_0_41_0 : expNegUpper (35398857793262565474239 / 528707486821847552000 : ℝ) ≤ (4186342417774105953116184832661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1687207 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_41_1 : expNegUpper (3538858463132039310423 / 52870748682184755200 : ℝ) ≤ (8536962899068473149067693172819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_41 : rowCell 0 41 ≤ (308266676267471310977614988327 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4186342417774105953116184832661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8536962899068473149067693172819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_41_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_41_1
  · norm_num [gridPoint]

theorem exp_0_42_0 : expNegUpper (3571827908629483118343 / 53363312681613363200 : ℝ) ≤ (8536947802969488540774400371111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686951 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_42_1 : expNegUpper (35708724288540184860061 / 533633126816133632000 : ℝ) ≤ (1738236011358922765698679748151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337343 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_42 : rowCell 0 42 ≤ (314072640482530587894432575069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8536947802969488540774400371111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1738236011358922765698679748151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_42_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_42_1
  · norm_num [gridPoint]

theorem exp_0_43_0 : expNegUpper (4004428755852135993581 / 59842400568463872000 : ℝ) ≤ (4345582484877350967684076424979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337343 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_43_1 : expNegUpper (1000861824996712571533 / 14960600142115968000 : ℝ) ≤ (34511254911844969576285393327 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_43 : rowCell 0 43 ≤ (159751879617954288740595926803 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4345582484877350967684076424979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34511254911844969576285393327 / 3906250000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_43_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_43_1
  · norm_num [gridPoint]

theorem exp_0_44_0 : expNegUpper (363636069347243904797 / 5435529217219712000 : ℝ) ≤ (8834866200830577715922788836739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1686499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_44_1 : expNegUpper (1454219954307337719147 / 21742116868878848000 : ℝ) ≤ (4483821039116272108834819853031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (843151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_44 : rowCell 0 44 ≤ (1298174898150314822171172101289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8834866200830577715922788836739 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4483821039116272108834819853031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_44_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_44_1
  · norm_num [gridPoint]

theorem exp_0_45_0 : expNegUpper (36689533474798977524907 / 548547076633522688000 : ℝ) ≤ (8967627073020731554327338678137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (843151 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_45_1 : expNegUpper (18341076877142101399793 / 274273538316761344000 : ℝ) ≤ (2272271409952496001092132180249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13489 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_45 : rowCell 0 45 ≤ (329177928461860928096528104141 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8967627073020731554327338678137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2272271409952496001092132180249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_45_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_45_1
  · norm_num [gridPoint]

theorem exp_0_46_0 : expNegUpper (2056536023068423989273 / 30753559436157184000 : ℝ) ≤ (1817814141286748830810019947507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (13489 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_46_1 : expNegUpper (822466675156057305933 / 12301423774462873600 : ℝ) ≤ (9198884074107725722914270453447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_46 : rowCell 0 46 ≤ (1333574093181457126155084459503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1817814141286748830810019947507 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9198884074107725722914270453447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_46_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_46_1
  · norm_num [gridPoint]

theorem exp_0_47_0 : expNegUpper (7469592349672200010957 / 111720780274778214400 : ℝ) ≤ (9198869232433170827900372893721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_47_1 : expNegUpper (2333878045827326100621 / 34912743835868192000 : ℝ) ≤ (4648379813214841845187358690291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421457 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_47 : rowCell 0 47 ≤ (1348717873554832236068475845579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9198869232433170827900372893721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4648379813214841845187358690291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_47_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_47_1
  · norm_num [gridPoint]

theorem exp_0_48_0 : expNegUpper (2355030216657858062349 / 35229160700169248000 : ℝ) ≤ (9296744895675542003627129285657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421457 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_48_1 : expNegUpper (37675308800266766057503 / 563666571202707968000 : ℝ) ≤ (9382485392629076223686400812907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_48 : rowCell 0 48 ≤ (1362106254744134909816141216787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9296744895675542003627129285657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9382485392629076223686400812907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_48_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_48_1
  · norm_num [gridPoint]

theorem exp_0_49_0 : expNegUpper (6758261966589238287 / 101111480771072000 : ℝ) ≤ (4691235395652349319432066674421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685707 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_49_1 : expNegUpper (3378736940039988519 / 50555740385536000 : ℝ) ≤ (4727942847991749529055412119381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421401 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_49 : rowCell 0 49 ≤ (1373709880138961924053532283227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4691235395652349319432066674421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4727942847991749529055412119381 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_49_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_49_1
  · norm_num [gridPoint]

theorem exp_0_50_0 : expNegUpper (618583742376062191681 / 9255813318993664000 : ℝ) ≤ (236396781045822699742201131963 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421401 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_50_1 : expNegUpper (1237048517778231570411 / 18511626637987328000 : ℝ) ≤ (2379209027883624425676281384937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21069 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_50 : rowCell 0 50 ≤ (691753432999657007058930887779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (236396781045822699742201131963 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2379209027883624425676281384937 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_50_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_50_1
  · norm_num [gridPoint]

theorem exp_0_51_0 : expNegUpper (38691398854618547286189 / 578991610523689472000 : ℝ) ≤ (4758410910743305009720221412359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21069 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_51_1 : expNegUpper (1934422960981566815927 / 28949580526184473600 : ℝ) ≤ (239131578717307697927710788429 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_51 : rowCell 0 51 ≤ (695741390043081045527363768299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4758410910743305009720221412359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (239131578717307697927710788429 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_51_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_51_1
  · norm_num [gridPoint]

theorem exp_0_52_0 : expNegUpper (216849189090617701663 / 3245253519864038400 : ℝ) ≤ (1195656129852175817983343130181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685453 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_52_1 : expNegUpper (4336740674811887830579 / 64905070397280768000 : ℝ) ≤ (4800571802839664133790441338601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_52 : rowCell 0 52 ≤ (698815285721296721242971586611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1195656129852175817983343130181 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4800571802839664133790441338601 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_52_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_52_1
  · norm_num [gridPoint]

theorem exp_0_53_0 : expNegUpper (39376567564732419652739 / 589322494933119488000 : ℝ) ≤ (4800564845575901231417465657379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685403 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_53_1 : expNegUpper (19687567302245393940909 / 294661247466559744000 : ℝ) ≤ (1924900722377698981527052738553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_53 : rowCell 0 53 ≤ (280390090697523836904371080353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4800564845575901231417465657379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1924900722377698981527052738553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_53_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_53_1
  · norm_num [gridPoint]

theorem exp_0_54_0 : expNegUpper (794450988644417881509 / 11890443891929344000 : ℝ) ≤ (4812244953477908767279924593891 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685371 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_54_1 : expNegUpper (1588874992220855010697 / 23780887783858688000 : ℝ) ≤ (2408854344112352845801706197589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_54 : rowCell 0 54 ≤ (702224871464429613534450836241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4812244953477908767279924593891 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2408854344112352845801706197589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_54_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_54_1
  · norm_num [gridPoint]

theorem exp_0_55_0 : expNegUpper (4452312181235028477393 / 66638303618396672000 : ℝ) ≤ (4817701947203636546325402881027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421339 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_55_1 : expNegUpper (556540231510241657793 / 8329787952299584000 : ℝ) ≤ (1204250707901864227502076833039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (842679 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_55 : rowCell 0 55 ≤ (1405142657301959295855262647127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4817701947203636546325402881027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1204250707901864227502076833039 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_55_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_55_1
  · norm_num [gridPoint]

theorem exp_0_56_0 : expNegUpper (5052669769219269130633 / 75623763605053504000 : ℝ) ≤ (9633992416388389259216199197381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (842679 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_56_1 : expNegUpper (8084442037295501378379 / 120998021768085606400 : ℝ) ≤ (240510850349933562095287842273 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_56 : rowCell 0 56 ≤ (351012518550618402095610925069 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9633992416388389259216199197381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (240510850349933562095287842273 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_56_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_56_1
  · norm_num [gridPoint]

theorem exp_0_57_0 : expNegUpper (8154840998495246210019 / 122051664684208230400 : ℝ) ≤ (601276313357995167239719308473 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685377 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_57_1 : expNegUpper (20387912675540172294443 / 305129161710520576000 : ℝ) ≤ (9594910743195098270373410308339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421353 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_57 : rowCell 0 57 ≤ (700599627744726023962092875421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (601276313357995167239719308473 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9594910743195098270373410308339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_57_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_57_1
  · norm_num [gridPoint]

theorem exp_0_58_0 : expNegUpper (2284964452201118724483 / 34197187572633856000 : ℝ) ≤ (383795919993335454125239190913 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (421353 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_58_1 : expNegUpper (4570194683876062131237 / 68394375145267712000 : ℝ) ≤ (2389421181989527683530459353851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_58 : rowCell 0 58 ≤ (1396623539909100467775639758069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (383795919993335454125239190913 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2389421181989527683530459353851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_58_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_58_1
  · norm_num [gridPoint]

theorem exp_0_59_0 : expNegUpper (1659473343500980709837 / 24834530699981312000 : ℝ) ≤ (298677257839435794405075308663 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685463 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_59_1 : expNegUpper (414900005902287973977 / 6208632674995328000 : ℝ) ≤ (237726075468785419957940958089 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (168553 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_59 : rowCell 0 59 ≤ (1390362007712206416285019999219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (298677257839435794405075308663 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (237726075468785419957940958089 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_59_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_59_1
  · norm_num [gridPoint]

theorem exp_0_60_0 : expNegUpper (10461658832132004973713 / 156549999249352832000 : ℝ) ≤ (594314426018072455265600289619 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (168553 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_60_1 : expNegUpper (41850580649451705967651 / 626199996997411328000 : ℝ) ≤ (944930829559834694383343338821 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685613 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_60 : rowCell 0 60 ≤ (172807390115204098822898990741 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (594314426018072455265600289619 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (944930829559834694383343338821 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_60_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_60_1
  · norm_num [gridPoint]

theorem exp_0_61_0 : expNegUpper (4689863928329921135171 / 70173284977893888000 : ℝ) ≤ (9449296375157042538261005985169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1685613 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_61_1 : expNegUpper (93807782944204292489 / 1403465699557877760 : ℝ) ≤ (9378836195431085933432952134271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (105357 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_61 : rowCell 0 61 ≤ (1372964342947642715927597213611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9449296375157042538261005985169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9378836195431085933432952134271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_61_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_61_1
  · norm_num [gridPoint]

theorem exp_0_62_0 : expNegUpper (851465273183739508801 / 12738839418208675840 : ℝ) ≤ (9378824563429191409049676304619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (105357 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_62_1 : expNegUpper (42578775608888121083961 / 636941970910433792000 : ℝ) ≤ (4649006267930762407725848338253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (842913 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_62 : rowCell 0 62 ≤ (340482935312777605273374517059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9378824563429191409049676304619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4649006267930762407725848338253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_62_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_62_1
  · norm_num [gridPoint]

theorem exp_0_63_0 : expNegUpper (42940110233519722294449 / 642347215325577728000 : ℝ) ≤ (4649000598882938118015938486771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (842913 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_63_1 : expNegUpper (671037663965295642007 / 10036675239462152000 : ℝ) ≤ (9207250460326518826939757915443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (337191 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_63 : rowCell 0 63 ≤ (337354894180033503844520251171 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4649000598882938118015938486771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9207250460326518826939757915443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_63_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_63_1
  · norm_num [gridPoint]

theorem sum_0_32_2 : blockSum (rowCell 0) 32 2 ≤ (1973339569549984175233201322913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_32) (by simpa only [blockSum_one] using cell_0_33) (by norm_num)

theorem sum_0_34_2 : blockSum (rowCell 0) 34 2 ≤ (420385601625961574244656301241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_34) (by simpa only [blockSum_one] using cell_0_35) (by norm_num)

theorem sum_0_32_4 : blockSum (rowCell 0) 32 4 ≤ (2037633788839896023228241414559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_32_2 sum_0_34_2 (by norm_num)

theorem sum_0_36_2 : blockSum (rowCell 0) 36 2 ≤ (2223876915865092543676913796709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_36) (by simpa only [blockSum_one] using cell_0_37) (by norm_num)

theorem sum_0_38_2 : blockSum (rowCell 0) 38 2 ≤ (467512123586759113467235329861 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_38) (by simpa only [blockSum_one] using cell_0_39) (by norm_num)

theorem sum_0_36_4 : blockSum (rowCell 0) 36 4 ≤ (2280718766899444055506545223007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_36_2 sum_0_38_2 (by norm_num)

theorem sum_0_32_8 : blockSum (rowCell 0) 32 8 ≤ (2159176277869670039367393318783 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_32_4 sum_0_36_4 (by norm_num)

theorem sum_0_40_2 : blockSum (rowCell 0) 40 2 ≤ (2441481910511810600763751858607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_40) (by simpa only [blockSum_one] using cell_0_41) (by norm_num)

theorem sum_0_42_2 : blockSum (rowCell 0) 42 2 ≤ (25343055988737566615024977147 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_42) (by simpa only [blockSum_one] using cell_0_43) (by norm_num)

theorem sum_0_40_4 : blockSum (rowCell 0) 40 4 ≤ (4975787509385567262266249573307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_40_2 sum_0_42_2 (by norm_num)

theorem sum_0_44_2 : blockSum (rowCell 0) 44 2 ≤ (2614886611997758534557284517853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_44) (by simpa only [blockSum_one] using cell_0_45) (by norm_num)

theorem sum_0_46_2 : blockSum (rowCell 0) 46 2 ≤ (1341145983368144681111780152541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_46) (by simpa only [blockSum_one] using cell_0_47) (by norm_num)

theorem sum_0_44_4 : blockSum (rowCell 0) 44 4 ≤ (1059435715746809579356168964587 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_44_2 sum_0_46_2 (by norm_num)

theorem sum_0_40_8 : blockSum (rowCell 0) 40 8 ≤ (5136483044059807579523547198121 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_40_4 sum_0_44_4 (by norm_num)

theorem sum_0_32_16 : blockSum (rowCell 0) 32 16 ≤ (9454835599799147658258333835687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_32_8 sum_0_40_8 (by norm_num)

theorem sum_0_48_2 : blockSum (rowCell 0) 48 2 ≤ (1367908067441548416934836750007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_48) (by simpa only [blockSum_one] using cell_0_49) (by norm_num)

theorem sum_0_50_2 : blockSum (rowCell 0) 50 2 ≤ (693747411521369026293147328039 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_50) (by simpa only [blockSum_one] using cell_0_51) (by norm_num)

theorem sum_0_48_4 : blockSum (rowCell 0) 48 4 ≤ (551080578096857293904226281217 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_48_2 sum_0_50_2 (by norm_num)

theorem sum_0_52_2 : blockSum (rowCell 0) 52 2 ≤ (2799581024930212627007798574987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_52) (by simpa only [blockSum_one] using cell_0_53) (by norm_num)

theorem sum_0_54_2 : blockSum (rowCell 0) 54 2 ≤ (2809592400230818522924164319609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_54) (by simpa only [blockSum_one] using cell_0_55) (by norm_num)

theorem sum_0_52_4 : blockSum (rowCell 0) 52 4 ≤ (1402293356290257787482990723649 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_52_2 sum_0_54_2 (by norm_num)

theorem sum_0_48_8 : blockSum (rowCell 0) 48 8 ≤ (5559989603064802044487112853383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_48_4 sum_0_52_4 (by norm_num)

theorem sum_0_56_2 : blockSum (rowCell 0) 56 2 ≤ (1402624664845962828153314725559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_56) (by simpa only [blockSum_one] using cell_0_57) (by norm_num)

theorem sum_0_58_2 : blockSum (rowCell 0) 58 2 ≤ (348373193452663360507582469661 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_58) (by simpa only [blockSum_one] using cell_0_59) (by norm_num)

theorem sum_0_56_4 : blockSum (rowCell 0) 56 4 ≤ (2796117438656616270183644604203 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_56_2 sum_0_58_2 (by norm_num)

theorem sum_0_60_2 : blockSum (rowCell 0) 60 2 ≤ (2755423463869275506510789139539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_60) (by simpa only [blockSum_one] using cell_0_61) (by norm_num)

theorem sum_0_62_2 : blockSum (rowCell 0) 62 2 ≤ (67783782949281110911789476823 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_62) (by simpa only [blockSum_one] using cell_0_63) (by norm_num)

theorem sum_0_60_4 : blockSum (rowCell 0) 60 4 ≤ (5466774781840519942982368212459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_60_2 sum_0_62_2 (by norm_num)

theorem sum_0_56_8 : blockSum (rowCell 0) 56 8 ≤ (2211801931830750496669931484173 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_56_4 sum_0_60_4 (by norm_num)

theorem sum_0_48_16 : blockSum (rowCell 0) 48 16 ≤ (22178988865283356572323883127631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_48_8 sum_0_56_8 (by norm_num)

theorem sum_0_32_32 : blockSum (rowCell 0) 32 32 ≤ (8217732012976330377768110159801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_32_16 sum_0_48_16 (by norm_num)

#print axioms sum_0_32_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
