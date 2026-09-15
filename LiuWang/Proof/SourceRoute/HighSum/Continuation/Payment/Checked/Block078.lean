import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_448_0 : expNegUpper (7348455462527907255281 / 69068228504552712000 : ℝ) ≤ (62236023105409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1148041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_448_1 : expNegUpper (470834170553543700282703 / 4420366624291373568000 : ℝ) ≤ (55166230962273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1149123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_448 : rowCell 4 448 ≤ (2140269461301 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62236023105409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55166230962273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_448_1
  · norm_num [gridPoint]

theorem exp_4_449_0 : expNegUpper (30230329513864268879 / 283813597102592000 : ℝ) ≤ (13791557292053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1149123 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_449_1 : expNegUpper (15132287795115224623 / 141906798551296000 : ℝ) ≤ (190998359043 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_449 : rowCell 4 449 ≤ (7588280611381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13791557292053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (190998359043 / 3906250000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_449_1
  · norm_num [gridPoint]

theorem exp_4_450_0 : expNegUpper (237201436505821841954711 / 2224415561735190784000 : ℝ) ≤ (48895578335049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2300413 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_450_1 : expNegUpper (474940045277108733343141 / 4448831123470381568000 : ℝ) ≤ (43334209694723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (287823 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_450 : rowCell 4 450 ≤ (840684875729 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (48895578335049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43334209694723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_450_1
  · norm_num [gridPoint]

theorem exp_4_451_0 : expNegUpper (476463082666668159092189 / 4463097630518518272000 : ℝ) ≤ (21667104151707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (287823 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_451_1 : expNegUpper (23850116779257811931747 / 223154881525925913600 : ℝ) ≤ (4800288415067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2304759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_451 : rowCell 4 451 ≤ (119206003089 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21667104151707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4800288415067 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_451_1
  · norm_num [gridPoint]

theorem exp_4_452_0 : expNegUpper (23926476880577063675587 / 223869348793620505600 : ℝ) ≤ (7680461219087 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2304759 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_452_1 : expNegUpper (479070874513831932073211 / 4477386975872410112000 : ℝ) ≤ (34028991859281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_452 : rowCell 4 452 ≤ (5281755321853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7680461219087 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34028991859281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_452_1
  · norm_num [gridPoint]

theorem exp_4_453_0 : expNegUpper (15503298317374247545069 / 144893521275227648000 : ℝ) ≤ (3402899078061 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306937 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_453_1 : expNegUpper (7760414065410878393339 / 72446760637613824000 : ℝ) ≤ (30151320598893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1154559 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_453 : rowCell 4 453 ≤ (292505372987 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3402899078061 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30151320598893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_453_1
  · norm_num [gridPoint]

theorem exp_4_454_0 : expNegUpper (9653624466803760139549 / 90120683629949184000 : ℝ) ≤ (6030263929843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1154559 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_454_1 : expNegUpper (19329069528096898812217 / 180241367259898368000 : ℝ) ≤ (13356702560893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2311303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_454 : rowCell 4 454 ≤ (4146626819703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6030263929843 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13356702560893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_454_1
  · norm_num [gridPoint]

theorem exp_4_455_0 : expNegUpper (484766474108638919481737 / 4520392041768616448000 : ℝ) ≤ (26713404285733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2311303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_455_1 : expNegUpper (60664260368376826069687 / 565049005221077056000 : ℝ) ≤ (23665625204537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578373 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_455 : rowCell 4 455 ≤ (91842102321 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26713404285733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23665625204537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_455_1
  · norm_num [gridPoint]

theorem exp_4_456_0 : expNegUpper (60857251267036632267383 / 566846592543191104000 : ℝ) ≤ (4733124893713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578373 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_456_1 : expNegUpper (97481543256317904374459 / 906954548069105766400 : ℝ) ≤ (20963929787333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578921 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_456 : rowCell 4 456 ≤ (1627213596603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4733124893713 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20963929787333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_456_1
  · norm_num [gridPoint]

theorem exp_4_457_0 : expNegUpper (97791168283097813935699 / 909835255445639270400 : ℝ) ≤ (4192785827901 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578921 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_457_1 : expNegUpper (244753824099242928489443 / 2274588138614098176000 : ℝ) ≤ (18569215431231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2317879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_457 : rowCell 4 457 ≤ (1441396210079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4192785827901 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18569215431231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_457_1
  · norm_num [gridPoint]

theorem exp_4_458_0 : expNegUpper (245529988969282800414547 / 2281801326208309504000 : ℝ) ≤ (18569214861029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2317879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_458_1 : expNegUpper (491613888690042260606333 / 4563602652416619008000 : ℝ) ≤ (16446773728517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1160039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_458 : rowCell 4 458 ≤ (2553397347627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18569214861029 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16446773728517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_458_1
  · norm_num [gridPoint]

theorem exp_4_459_0 : expNegUpper (19726817187914451932797 / 183122074636431872000 : ℝ) ≤ (8223386613337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1160039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_459_1 : expNegUpper (4937264477485973794837 / 45780518659107968000 : ℝ) ≤ (145658000651 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2322281 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_459 : rowCell 4 459 ≤ (452292941459 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8223386613337 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (145658000651 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_459_1
  · norm_num [gridPoint]

theorem exp_4_460_0 : expNegUpper (123821801671428702220013 / 1148130979427682432000 : ℝ) ≤ (14565799623451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2322281 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_460_1 : expNegUpper (495845335366489860340051 / 4592523917710729728000 : ℝ) ≤ (12898956966117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2324487 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_460 : rowCell 4 460 ≤ (2002754725879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14565799623451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12898956966117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_460_1
  · norm_num [gridPoint]

theorem exp_4_461_0 : expNegUpper (497410318894464779238539 / 4607018807816417792000 : ℝ) ≤ (6449478288733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2324487 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_461_1 : expNegUpper (9959411230721166998089 / 92140376156328355840 : ℝ) ≤ (5710992998851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (290837 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_461 : rowCell 4 461 ≤ (1773504983429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6449478288733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5710992998851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_461_1
  · norm_num [gridPoint]

theorem exp_4_462_0 : expNegUpper (9990795526328997122489 / 92430730724557219840 : ℝ) ≤ (5710992827857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (290837 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_462_1 : expNegUpper (500102136249641494905961 / 4621536536227860992000 : ℝ) ≤ (2528340714739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2328909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_462 : rowCell 4 462 ≤ (314075392371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5710992827857 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2528340714739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_462_1
  · norm_num [gridPoint]

theorem exp_4_463_0 : expNegUpper (501675588944008686266849 / 4636077102945059328000 : ℝ) ≤ (316042579939 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2328909 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_463_1 : expNegUpper (31390004343723621379603 / 289754818934066208000 : ℝ) ≤ (8953990887219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1165563 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_463 : rowCell 4 463 ≤ (278081708811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (316042579939 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8953990887219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_463_1
  · norm_num [gridPoint]

theorem exp_4_464_0 : expNegUpper (1259544416923699790987 / 11626601269920032000 : ℝ) ≤ (8953990622473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1165563 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_464_1 : expNegUpper (20175374851128253525463 / 186025620318720512000 : ℝ) ≤ (7926928724623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466669 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_464 : rowCell 4 464 ≤ (615485902621 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8953990622473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7926928724623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_464_1
  · norm_num [gridPoint]

theorem exp_4_465_0 : expNegUpper (505966319785202193237367 / 4665226751296721408000 : ℝ) ≤ (792692849171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466669 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_465_1 : expNegUpper (253267525788932664911903 / 2332613375648360704000 : ℝ) ≤ (3508574180753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2335569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_465 : rowCell 4 465 ≤ (136216938807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (792692849171 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3508574180753 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_465_1
  · norm_num [gridPoint]

theorem exp_4_466_0 : expNegUpper (254060628991757081761807 / 2339917916465592576000 : ℝ) ≤ (701714815661 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2335569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_466_1 : expNegUpper (101738424078178712772881 / 935967166586237030400 : ℝ) ≤ (6211320188781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584449 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_466 : rowCell 4 466 ≤ (482315898349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (701714815661 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6211320188781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_466_1
  · norm_num [gridPoint]

theorem exp_4_467_0 : expNegUpper (102056518271350894796521 / 938893550574280806400 : ℝ) ≤ (194103750267 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584449 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_467_1 : expNegUpper (127713896927407421746859 / 1173616938217851008000 : ℝ) ≤ (5497622062391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1170013 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_467 : rowCell 4 467 ≤ (426913287783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (194103750267 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5497622062391 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_467_1
  · norm_num [gridPoint]

theorem exp_4_468_0 : expNegUpper (128112582474315442835851 / 1177280627779344512000 : ℝ) ≤ (5497621903857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1170013 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_468_1 : expNegUpper (513025463526412345921963 / 4709122511117378048000 : ℝ) ≤ (4865569713363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117113 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_468 : rowCell 4 468 ≤ (47230827713 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5497621903857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4865569713363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_468_1
  · norm_num [gridPoint]

theorem exp_4_469_0 : expNegUpper (20584979343894988093403 / 188952004306764288000 : ℝ) ≤ (2432784786963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117113 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_469_1 : expNegUpper (10304035156671603747941 / 94476002153382144000 : ℝ) ≤ (4305866131229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2344497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_469 : rowCell 4 469 ≤ (334394665791 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2432784786963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4305866131229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_469_1
  · norm_num [gridPoint]

theorem exp_4_470_0 : expNegUpper (11234892661944172036667 / 103010881359273728000 : ℝ) ≤ (2152933004299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2344497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_470_1 : expNegUpper (22494977418411819919207 / 206021762718547456000 : ℝ) ≤ (952566952639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1173369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_470 : rowCell 4 470 ≤ (147958942483 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2152933004299 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (952566952639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_470_1
  · norm_num [gridPoint]

theorem exp_4_471_0 : expNegUpper (518992076445772052127289 / 4753223815689830912000 : ℝ) ≤ (3810267702711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1173369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_471_1 : expNegUpper (12989341047210650122129 / 118830595392245772800 : ℝ) ≤ (3371465983571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1174491 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_471 : rowCell 4 471 ≤ (523698472743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3810267702711 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3371465983571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_471_1
  · norm_num [gridPoint]

theorem exp_4_472_0 : expNegUpper (13029638389468344109649 / 119199248178970636800 : ℝ) ≤ (674293177747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1174491 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_472_1 : expNegUpper (521769251620781274356311 / 4767969927158825472000 : ℝ) ≤ (1491490584757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235123 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_472 : rowCell 4 472 ≤ (231685994281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (674293177747 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1491490584757 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_472_1
  · norm_num [gridPoint]

theorem exp_4_473_0 : expNegUpper (523385449840655697191759 / 4782738876933575168000 : ℝ) ≤ (745745271531 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235123 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_473_1 : expNegUpper (261985659906438156642139 / 2391369438466787584000 : ℝ) ≤ (2639069556151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2353481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_473 : rowCell 4 473 ≤ (51245622987 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (745745271531 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2639069556151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_473_1
  · norm_num [gridPoint]

theorem exp_4_474_0 : expNegUpper (420473463379101197819 / 3838024532011264000 : ℝ) ≤ (2639069482829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2353481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_474_1 : expNegUpper (841887770331279629437 / 7676049064022528000 : ℝ) ≤ (1167319946693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294467 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_474 : rowCell 4 474 ≤ (362687356281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2639069482829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1167319946693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_474_1
  · norm_num [gridPoint]

theorem exp_4_475_0 : expNegUpper (527804683720734811360997 / 4812345291400339968000 : ℝ) ≤ (1167319914461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (294467 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_475_1 : expNegUpper (132098717886410071606729 / 1203086322850084992000 : ℝ) ≤ (2065179725299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1178997 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_475 : rowCell 4 475 ≤ (320838794857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1167319914461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2065179725299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_475_1
  · norm_num [gridPoint]

theorem exp_4_476_0 : expNegUpper (132506005830892321545641 / 1206795689023088768000 : ℝ) ≤ (16521437349 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1178997 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_476_1 : expNegUpper (106123275014197302819943 / 965436551218471014400 : ℝ) ≤ (36533798343 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36879 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_476 : rowCell 4 476 ≤ (283798626797 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16521437349 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36533798343 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_476_1
  · norm_num [gridPoint]

theorem exp_4_477_0 : expNegUpper (106449971604943713693503 / 968408611818025062400 : ℝ) ≤ (28542029177 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36879 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_477_1 : expNegUpper (266422188512713549072793 / 2421021529545062656000 : ℝ) ≤ (1615626549853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2362521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_477 : rowCell 4 477 ≤ (251016805847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28542029177 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1615626549853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_477_1
  · norm_num [gridPoint]

theorem exp_4_478_0 : expNegUpper (267241098908260652472457 / 2428463100196825344000 : ℝ) ≤ (1615626506057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2362521 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_478_1 : expNegUpper (535078887401300685293593 / 4856926200393650688000 : ℝ) ≤ (89303084841 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_478 : rowCell 4 478 ≤ (222005915239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1615626506057 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (89303084841 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_478_1
  · norm_num [gridPoint]

theorem exp_4_479_0 : expNegUpper (21468842107652645693753 / 194873287200117248000 : ℝ) ≤ (1428849318961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_479_1 : expNegUpper (671649895238682402841 / 6089790225003664000 : ℝ) ≤ (1263575974917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2367061 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_479 : rowCell 4 479 ≤ (98167035703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1428849318961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1263575974917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_479_1
  · norm_num [gridPoint]

theorem sum_4_448_2 : blockSum (rowCell 4) 448 2 ≤ (3229871691317 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_448) (by simpa only [blockSum_one] using cell_4_449) (by norm_num)

theorem sum_4_450_2 : blockSum (rowCell 4) 450 2 ≤ (6342889580141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_450) (by simpa only [blockSum_one] using cell_4_451) (by norm_num)

theorem sum_4_448_4 : blockSum (rowCell 4) 448 4 ≤ (28835137616867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_448_2 sum_4_450_2 (by norm_num)

theorem sum_4_452_2 : blockSum (rowCell 4) 452 2 ≤ (1992368257929 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_452) (by simpa only [blockSum_one] using cell_4_453) (by norm_num)

theorem sum_4_454_2 : blockSum (rowCell 4) 454 2 ≤ (7820310912543 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_454) (by simpa only [blockSum_one] using cell_4_455) (by norm_num)

theorem sum_4_452_4 : blockSum (rowCell 4) 452 4 ≤ (4445538050547 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_452_2 sum_4_454_2 (by norm_num)

theorem sum_4_448_8 : blockSum (rowCell 4) 448 8 ≤ (9323457963811 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_448_4 sum_4_452_4 (by norm_num)

theorem sum_4_456_2 : blockSum (rowCell 4) 456 2 ≤ (1534304903341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_456) (by simpa only [blockSum_one] using cell_4_457) (by norm_num)

theorem sum_4_458_2 : blockSum (rowCell 4) 458 2 ≤ (2407431027461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_458) (by simpa only [blockSum_one] using cell_4_459) (by norm_num)

theorem sum_4_456_4 : blockSum (rowCell 4) 456 4 ≤ (5476040834143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_456_2 sum_4_458_2 (by norm_num)

theorem sum_4_460_2 : blockSum (rowCell 4) 460 2 ≤ (944064927327 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_460) (by simpa only [blockSum_one] using cell_4_461) (by norm_num)

theorem sum_4_462_2 : blockSum (rowCell 4) 462 2 ≤ (296078550591 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_462) (by simpa only [blockSum_one] using cell_4_463) (by norm_num)

theorem sum_4_460_4 : blockSum (rowCell 4) 460 4 ≤ (3368522607609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_460_2 sum_4_462_2 (by norm_num)

theorem sum_4_456_8 : blockSum (rowCell 4) 456 8 ≤ (1105570430219 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_456_4 sum_4_460_4 (by norm_num)

theorem sum_4_448_16 : blockSum (rowCell 4) 448 16 ≤ (64306416702559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_448_8 sum_4_456_8 (by norm_num)

theorem sum_4_464_2 : blockSum (rowCell 4) 464 2 ≤ (1160353657849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_464) (by simpa only [blockSum_one] using cell_4_465) (by norm_num)

theorem sum_4_466_2 : blockSum (rowCell 4) 466 2 ≤ (227307296533 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_466) (by simpa only [blockSum_one] using cell_4_467) (by norm_num)

theorem sum_4_464_4 : blockSum (rowCell 4) 464 4 ≤ (2069582843981 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_464_2 sum_4_466_2 (by norm_num)

theorem sum_4_468_2 : blockSum (rowCell 4) 468 2 ≤ (142448257499 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_468) (by simpa only [blockSum_one] using cell_4_469) (by norm_num)

theorem sum_4_470_2 : blockSum (rowCell 4) 470 2 ≤ (44621369707 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_470) (by simpa only [blockSum_one] using cell_4_471) (by norm_num)

theorem sum_4_468_4 : blockSum (rowCell 4) 468 4 ≤ (508003363533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_468_2 sum_4_470_2 (by norm_num)

theorem sum_4_464_8 : blockSum (rowCell 4) 464 8 ≤ (6679182505627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_464_4 sum_4_468_4 (by norm_num)

theorem sum_4_472_2 : blockSum (rowCell 4) 472 2 ≤ (436668486229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_472) (by simpa only [blockSum_one] using cell_4_473) (by norm_num)

theorem sum_4_474_2 : blockSum (rowCell 4) 474 2 ≤ (341763075569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_474) (by simpa only [blockSum_one] using cell_4_475) (by norm_num)

theorem sum_4_472_4 : blockSum (rowCell 4) 472 4 ≤ (389215780899 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_472_2 sum_4_474_2 (by norm_num)

theorem sum_4_476_2 : blockSum (rowCell 4) 476 2 ≤ (133703858161 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_476) (by simpa only [blockSum_one] using cell_4_477) (by norm_num)

theorem sum_4_478_2 : blockSum (rowCell 4) 478 2 ≤ (83667997329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_478) (by simpa only [blockSum_one] using cell_4_479) (by norm_num)

theorem sum_4_476_4 : blockSum (rowCell 4) 476 4 ≤ (953155419289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_476_2 sum_4_478_2 (by norm_num)

theorem sum_4_472_8 : blockSum (rowCell 4) 472 8 ≤ (502003708577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_472_4 sum_4_476_4 (by norm_num)

theorem sum_4_464_16 : blockSum (rowCell 4) 464 16 ≤ (143581266383 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_464_8 sum_4_472_8 (by norm_num)

theorem sum_4_448_32 : blockSum (rowCell 4) 448 32 ≤ (73495617751071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_448_16 sum_4_464_16 (by norm_num)

#print axioms sum_4_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
