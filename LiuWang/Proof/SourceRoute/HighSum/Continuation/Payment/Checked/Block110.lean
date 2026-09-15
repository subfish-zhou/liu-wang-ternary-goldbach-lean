import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_448_0 : expNegUpper (388625184795643118699 / 3635169921292248000 : ℝ) ≤ (9316334345189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23053 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_448_1 : expNegUpper (24899873936636821278037 / 232650874962703872000 : ℝ) ≤ (4132418149141 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1153729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_448 : rowCell 6 448 ≤ (256406951781 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9316334345189 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4132418149141 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_448_1
  · norm_num [gridPoint]

theorem exp_6_449_0 : expNegUpper (30375655336384334927 / 283813597102592000 : ℝ) ≤ (33059344082947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1153729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_449_1 : expNegUpper (15204834198626135599 / 141906798551296000 : ℝ) ≤ (29325612896307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_449 : rowCell 6 449 ≤ (568645888989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33059344082947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29325612896307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_449_1
  · norm_num [gridPoint]

theorem exp_6_450_0 : expNegUpper (238338614927839889954711 / 2224415561735190784000 : ℝ) ≤ (29325611917811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_450_1 : expNegUpper (477210761253984765343141 / 4448831123470381568000 : ℝ) ≤ (13005702087311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (288973 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_450 : rowCell 6 450 ≤ (4035224930311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29325611917811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13005702087311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_450_1
  · norm_num [gridPoint]

theorem exp_6_451_0 : expNegUpper (478741080377864319092189 / 4463097630518518272000 : ℝ) ≤ (5202280662451 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (288973 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_451_1 : expNegUpper (23963834621459616731747 / 223154881525925913600 : ℝ) ≤ (5767459172141 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_451 : rowCell 6 451 ≤ (3579048117287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5202280662451 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5767459172141 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_451_1
  · norm_num [gridPoint]

theorem exp_6_452_0 : expNegUpper (24040558809494874875587 / 223869348793620505600 : ℝ) ≤ (23069835928597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_452_1 : expNegUpper (481348872225028092073211 / 4477386975872410112000 : ℝ) ≤ (20459237229693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18529 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_452 : rowCell 6 452 ≤ (634835824571 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23069835928597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20459237229693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_452_1
  · norm_num [gridPoint]

theorem exp_6_453_0 : expNegUpper (15577017009165095545069 / 144893521275227648000 : ℝ) ≤ (20459236560017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18529 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_453_1 : expNegUpper (7797214687642430393339 / 72446760637613824000 : ℝ) ≤ (18142566447683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23183 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_453 : rowCell 6 453 ≤ (2814878156629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20459236560017 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18142566447683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_453_1
  · norm_num [gridPoint]

theorem exp_6_454_0 : expNegUpper (9699402873057287179549 / 90120683629949184000 : ℝ) ≤ (4535641464403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (23183 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_454_1 : expNegUpper (19420480705917550332217 / 180241367259898368000 : ℝ) ≤ (502715834301 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_454 : rowCell 6 454 ≤ (2496043891771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4535641464403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (502715834301 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_454_1
  · norm_num [gridPoint]

theorem exp_6_455_0 : expNegUpper (487059035288475335481737 / 4520392041768616448000 : ℝ) ≤ (16086906177741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_455_1 : expNegUpper (60950375407461370069687 / 565049005221077056000 : ℝ) ≤ (1782875766201 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1161331 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_455 : rowCell 6 455 ≤ (276642859119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16086906177741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1782875766201 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_455_1
  · norm_num [gridPoint]

theorem exp_6_456_0 : expNegUpper (61144276522911192267383 / 566846592543191104000 : ℝ) ≤ (14263005671581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1161331 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_456_1 : expNegUpper (97940055492285187574459 / 906954548069105766400 : ℝ) ≤ (1580609110793 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (145303 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_456 : rowCell 6 456 ≤ (490536669873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14263005671581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1580609110793 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_456_1
  · norm_num [gridPoint]

theorem exp_6_457_0 : expNegUpper (98251136865929122735699 / 909835255445639270400 : ℝ) ≤ (252897449657 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (145303 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_457_1 : expNegUpper (245901925122741168489443 / 2274588138614098176000 : ℝ) ≤ (11209413939153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163519 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_457 : rowCell 6 457 ≤ (869737998739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (252897449657 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11209413939153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_457_1
  · norm_num [gridPoint]

theorem exp_6_458_0 : expNegUpper (246681730859941104414547 / 2281801326208309504000 : ℝ) ≤ (2802353395931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163519 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_458_1 : expNegUpper (493913731604198804606333 / 4563602652416619008000 : ℝ) ≤ (4968056842449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_458 : rowCell 6 458 ≤ (1541950846363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2802353395931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4968056842449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_458_1
  · norm_num [gridPoint]

theorem exp_6_459_0 : expNegUpper (19819102173853518812797 / 183122074636431872000 : ℝ) ≤ (9936113371829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329231 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_459_1 : expNegUpper (4960299315299139874837 / 45780518659107968000 : ℝ) ≤ (8806747955913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (582857 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_459 : rowCell 6 459 ≤ (1366746287309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9936113371829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8806747955913 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_459_1
  · norm_num [gridPoint]

theorem exp_6_460_0 : expNegUpper (124399493050337886220013 / 1148130979427682432000 : ℝ) ≤ (550421730011 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (582857 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_460_1 : expNegUpper (498152460014966532340051 / 4592523917710729728000 : ℝ) ≤ (3902564783441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (583407 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_460 : rowCell 6 460 ≤ (1211353013589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (550421730011 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3902564783441 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_460_1
  · norm_num [gridPoint]

theorem exp_6_461_0 : expNegUpper (499724725277261579238539 / 4607018807816417792000 : ℝ) ≤ (3902564662021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (583407 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_461_1 : expNegUpper (10005626541033901718089 / 92140376156328355840 : ℝ) ≤ (6916881943879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2335831 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_461 : rowCell 6 461 ≤ (67096393029 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3902564662021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6916881943879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_461_1
  · norm_num [gridPoint]

theorem exp_6_462_0 : expNegUpper (10037156471328134402489 / 92430730724557219840 : ℝ) ≤ (6916881730027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2335831 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_462_1 : expNegUpper (502416542632438294905961 / 4621536536227860992000 : ℝ) ≤ (6129237756621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2338039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_462 : rowCell 6 462 ≤ (95133475409 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6916881730027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6129237756621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_462_1
  · norm_num [gridPoint]

theorem exp_6_463_0 : expNegUpper (503997277061125614266849 / 4636077102945059328000 : ℝ) ≤ (1532309392077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2338039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_463_1 : expNegUpper (31534882296845925379603 / 289754818934066208000 : ℝ) ≤ (5430859810173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_463 : rowCell 6 463 ≤ (52685792929 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1532309392077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5430859810173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_463_1
  · norm_num [gridPoint]

theorem exp_6_464_0 : expNegUpper (1265357739384392270987 / 11626601269920032000 : ℝ) ≤ (2715429822181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2340249 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_464_1 : expNegUpper (20268242375812930645463 / 186025620318720512000 : ℝ) ≤ (240584087569 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36601 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_464 : rowCell 6 464 ≤ (746895320861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2715429822181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (240584087569 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_464_1
  · norm_num [gridPoint]

theorem exp_6_465_0 : expNegUpper (508295289636639249237367 / 4665226751296721408000 : ℝ) ≤ (481168160539 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36601 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_465_1 : expNegUpper (254430190281071160911903 / 2332613375648360704000 : ℝ) ≤ (852553282387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2344681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_465 : rowCell 6 465 ≤ (82714612781 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (481168160539 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (852553282387 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_465_1
  · norm_num [gridPoint]

theorem exp_6_466_0 : expNegUpper (255226934351055641761807 / 2339917916465592576000 : ℝ) ≤ (2131383141703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2344681 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_466_1 : expNegUpper (102204218048466123972881 / 935967166586237030400 : ℝ) ≤ (944044961951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2346903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_466 : rowCell 6 466 ≤ (586207174379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2131383141703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (944044961951 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_466_1
  · norm_num [gridPoint]

theorem exp_6_467_0 : expNegUpper (5395987820447491136659 / 49415450030225305600 : ℝ) ≤ (29501404177 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2346903 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_467_1 : expNegUpper (6752476295108247460361 / 61769312537781632000 : ℝ) ≤ (3344879346723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2349127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_467 : rowCell 6 467 ≤ (519274026041 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29501404177 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3344879346723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_467_1
  · norm_num [gridPoint]

theorem exp_6_468_0 : expNegUpper (128697555587544754835851 / 1177280627779344512000 : ℝ) ≤ (1672439623561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2349127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_468_1 : expNegUpper (515361715112169529921963 / 4709122511117378048000 : ℝ) ≤ (592522772903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (587839 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_468 : rowCell 6 468 ≤ (459948064589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1672439623561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (592522772903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_468_1
  · norm_num [gridPoint]

theorem exp_6_469_0 : expNegUpper (20678720676698080573403 / 188952004306764288000 : ℝ) ≤ (740653444211 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (587839 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_469_1 : expNegUpper (10350833005729948707941 / 94476002153382144000 : ℝ) ≤ (81994859983 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (588397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_469 : rowCell 6 469 ≤ (203684450881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (740653444211 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81994859983 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_469_1
  · norm_num [gridPoint]

theorem exp_6_470_0 : expNegUpper (259576118318334644843341 / 2369250271263295744000 : ℝ) ≤ (655958860573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (588397 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_470_1 : expNegUpper (519728013943549170141761 / 4738500542526591488000 : ℝ) ≤ (1161810462059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2355823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_470 : rowCell 6 470 ≤ (360772963219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (655958860573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1161810462059 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_470_1
  · norm_num [gridPoint]

theorem exp_6_471_0 : expNegUpper (521342891500169492127289 / 4753223815689830912000 : ℝ) ≤ (1161810428103 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2355823 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_471_1 : expNegUpper (13048020401891584522129 / 118830595392245772800 : ℝ) ≤ (411520253587 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1179031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_471 : rowCell 6 471 ≤ (319482653547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1161810428103 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (411520253587 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_471_1
  · norm_num [gridPoint]

theorem exp_6_472_0 : expNegUpper (13088499787507281709649 / 119199248178970636800 : ℝ) ≤ (2057601208169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1179031 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_472_1 : expNegUpper (524120066675178714356311 / 4767969927158825472000 : ℝ) ≤ (1821900183021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (147519 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_472 : rowCell 6 472 ≤ (35362090867 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2057601208169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1821900183021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_472_1
  · norm_num [gridPoint]

theorem exp_6_473_0 : expNegUpper (525743546629373265191759 / 4782738876933575168000 : ℝ) ≤ (1821900130429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (147519 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_473_1 : expNegUpper (263162887867216908642139 / 2391369438466787584000 : ℝ) ≤ (403269633013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47251 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_473 : rowCell 6 473 ≤ (125240865091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1821900130429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (403269633013 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_473_1
  · norm_num [gridPoint]

theorem exp_6_474_0 : expNegUpper (422362853503803303419 / 3838024532011264000 : ℝ) ≤ (806539242887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47251 / 20000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_474_1 : expNegUpper (845660725193227738237 / 7676049064022528000 : ℝ) ≤ (285617070333 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_474 : rowCell 6 474 ≤ (110882199661 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (806539242887 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (285617070333 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_474_1
  · norm_num [gridPoint]

theorem exp_6_475_0 : expNegUpper (530170062243772507360997 / 4812345291400339968000 : ℝ) ≤ (1428085310947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364799 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_475_1 : expNegUpper (132689152300379479606729 / 1203086322850084992000 : ℝ) ≤ (316053567303 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (591763 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_475 : rowCell 6 475 ≤ (196324904249 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1428085310947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (316053567303 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_475_1
  · norm_num [gridPoint]

theorem exp_6_476_0 : expNegUpper (133098260678441761545641 / 1206795689023088768000 : ℝ) ≤ (316053558347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (591763 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_476_1 : expNegUpper (106596350718804842019943 / 965436551218471014400 : ℝ) ≤ (559532392901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2369309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_476 : rowCell 6 476 ≤ (173790847307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (316053558347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (559532392901 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_476_1
  · norm_num [gridPoint]

theorem exp_6_477_0 : expNegUpper (106924503656415278493503 / 968408611818025062400 : ℝ) ≤ (559532377143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2369309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_477_1 : expNegUpper (267606698207812429072793 / 2421021529545062656000 : ℝ) ≤ (495253942737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148223 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_477 : rowCell 6 477 ≤ (153831932211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (559532377143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (495253942737 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_477_1
  · norm_num [gridPoint]

theorem exp_6_478_0 : expNegUpper (268429249470519596472457 / 2428463100196825344000 : ℝ) ≤ (247626964437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (148223 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_478_1 : expNegUpper (537451547658658509293593 / 4856926200393650688000 : ℝ) ≤ (876655489931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (296729 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_478 : rowCell 6 478 ≤ (136155228843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (247626964437 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (876655489931 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_478_1
  · norm_num [gridPoint]

theorem exp_6_479_0 : expNegUpper (21564039787319763773753 / 194873287200117248000 : ℝ) ≤ (876655465541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (296729 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_479_1 : expNegUpper (674620271644329762841 / 6089790225003664000 : ℝ) ≤ (775833331337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2376099 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_479 : rowCell 6 479 ≤ (120500967727 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (876655465541 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (775833331337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_479_1
  · norm_num [gridPoint]

theorem sum_6_448_2 : blockSum (rowCell 6) 448 2 ≤ (2419326536883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_448) (by simpa only [blockSum_one] using cell_6_449) (by norm_num)

theorem sum_6_450_2 : blockSum (rowCell 6) 450 2 ≤ (3807136523799 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_450) (by simpa only [blockSum_one] using cell_6_451) (by norm_num)

theorem sum_6_448_4 : blockSum (rowCell 6) 448 4 ≤ (1729157919513 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_448_2 sum_6_450_2 (by norm_num)

theorem sum_6_452_2 : blockSum (rowCell 6) 452 2 ≤ (1497264319871 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_452) (by simpa only [blockSum_one] using cell_6_453) (by norm_num)

theorem sum_6_454_2 : blockSum (rowCell 6) 454 2 ≤ (4709186764723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_454) (by simpa only [blockSum_one] using cell_6_455) (by norm_num)

theorem sum_6_452_4 : blockSum (rowCell 6) 452 4 ≤ (10698244044207 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_452_2 sum_6_454_2 (by norm_num)

theorem sum_6_448_8 : blockSum (rowCell 6) 448 8 ≤ (27989823239337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_448_4 sum_6_452_4 (by norm_num)

theorem sum_6_456_2 : blockSum (rowCell 6) 456 2 ≤ (370162267697 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_456) (by simpa only [blockSum_one] using cell_6_457) (by norm_num)

theorem sum_6_458_2 : blockSum (rowCell 6) 458 2 ≤ (363587141709 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_458) (by simpa only [blockSum_one] using cell_6_459) (by norm_num)

theorem sum_6_456_4 : blockSum (rowCell 6) 456 4 ≤ (3305159905321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_456_2 sum_6_458_2 (by norm_num)

theorem sum_6_460_2 : blockSum (rowCell 6) 460 2 ≤ (2284895302053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_460) (by simpa only [blockSum_one] using cell_6_461) (by norm_num)

theorem sum_6_462_2 : blockSum (rowCell 6) 462 2 ≤ (897153720477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_462) (by simpa only [blockSum_one] using cell_6_463) (by norm_num)

theorem sum_6_460_4 : blockSum (rowCell 6) 460 4 ≤ (4079202743007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_460_2 sum_6_462_2 (by norm_num)

theorem sum_6_456_8 : blockSum (rowCell 6) 456 8 ≤ (10689522553649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_456_4 sum_6_460_4 (by norm_num)

theorem sum_6_448_16 : blockSum (rowCell 6) 448 16 ≤ (19339672896493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_448_8 sum_6_456_8 (by norm_num)

theorem sum_6_464_2 : blockSum (rowCell 6) 464 2 ≤ (1408612223109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_464) (by simpa only [blockSum_one] using cell_6_465) (by norm_num)

theorem sum_6_466_2 : blockSum (rowCell 6) 466 2 ≤ (55274060021 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_466) (by simpa only [blockSum_one] using cell_6_467) (by norm_num)

theorem sum_6_464_4 : blockSum (rowCell 6) 464 4 ≤ (2514093423529 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_464_2 sum_6_466_2 (by norm_num)

theorem sum_6_468_2 : blockSum (rowCell 6) 468 2 ≤ (867316966351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_468) (by simpa only [blockSum_one] using cell_6_469) (by norm_num)

theorem sum_6_470_2 : blockSum (rowCell 6) 470 2 ≤ (340127808383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_470) (by simpa only [blockSum_one] using cell_6_471) (by norm_num)

theorem sum_6_468_4 : blockSum (rowCell 6) 468 4 ≤ (1547572583117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_468_2 sum_6_470_2 (by norm_num)

theorem sum_6_464_8 : blockSum (rowCell 6) 464 8 ≤ (2030833003323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_464_4 sum_6_468_4 (by norm_num)

theorem sum_6_472_2 : blockSum (rowCell 6) 472 2 ≤ (266689228559 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_472) (by simpa only [blockSum_one] using cell_6_473) (by norm_num)

theorem sum_6_474_2 : blockSum (rowCell 6) 474 2 ≤ (418089303571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_474) (by simpa only [blockSum_one] using cell_6_475) (by norm_num)

theorem sum_6_472_4 : blockSum (rowCell 6) 472 4 ≤ (951467760689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_472_2 sum_6_474_2 (by norm_num)

theorem sum_6_476_2 : blockSum (rowCell 6) 476 2 ≤ (163811389759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_476) (by simpa only [blockSum_one] using cell_6_477) (by norm_num)

theorem sum_6_478_2 : blockSum (rowCell 6) 478 2 ≤ (25665619657 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_478) (by simpa only [blockSum_one] using cell_6_479) (by norm_num)

theorem sum_6_476_4 : blockSum (rowCell 6) 476 4 ≤ (73034872011 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_476_2 sum_6_478_2 (by norm_num)

theorem sum_6_472_8 : blockSum (rowCell 6) 472 8 ≤ (1535746736777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_472_4 sum_6_476_4 (by norm_num)

theorem sum_6_464_16 : blockSum (rowCell 6) 464 16 ≤ (5597412743423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_464_8 sum_6_472_8 (by norm_num)

theorem sum_6_448_32 : blockSum (rowCell 6) 448 32 ≤ (44276758536409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_448_16 sum_6_464_16 (by norm_num)

#print axioms sum_6_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
