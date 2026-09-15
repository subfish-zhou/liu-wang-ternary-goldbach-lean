import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_448_0 : expNegUpper (7372070828254115255281 / 69068228504552712000 : ℝ) ≤ (11053266929703 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2302223 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_448_1 : expNegUpper (472343126715247636282703 / 4420366624291373568000 : ℝ) ≤ (9803036310729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2304383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_448 : rowCell 5 448 ≤ (6083441481509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11053266929703 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9803036310729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_448_1
  · norm_num [gridPoint]

theorem exp_5_449_0 : expNegUpper (30327213395544312911 / 283813597102592000 : ℝ) ≤ (39212143939977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2304383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_449_1 : expNegUpper (15180652064122498607 / 141906798551296000 : ℝ) ≤ (8693498979077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_449 : rowCell 5 449 ≤ (5395135790243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39212143939977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8693498979077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_449_1
  · norm_num [gridPoint]

theorem exp_5_450_0 : expNegUpper (237959555453833873954711 / 2224415561735190784000 : ℝ) ≤ (34773994768231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306547 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_450_1 : expNegUpper (476453855928359421343141 / 4448831123470381568000 : ℝ) ≤ (30835629943783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1154357 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_450 : rowCell 5 450 ≤ (1196078195037 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34773994768231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30835629943783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_450_1
  · norm_num [gridPoint]

theorem exp_5_451_0 : expNegUpper (477981747807465599092189 / 4463097630518518272000 : ℝ) ≤ (30835628932237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1154357 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_451_1 : expNegUpper (23925928674059015131747 / 223154881525925913600 : ℝ) ≤ (341763332701 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (577721 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_451 : rowCell 5 451 ≤ (4242296907509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30835628932237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341763332701 / 12500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_451_1
  · norm_num [gridPoint]

theorem exp_5_452_0 : expNegUpper (24002531499855604475587 / 223869348793620505600 : ℝ) ≤ (27341065724891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (577721 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_452_1 : expNegUpper (480589539654629372073211 / 4477386975872410112000 : ℝ) ≤ (6060140062293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1156529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_452 : rowCell 5 452 ≤ (117543078403 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27341065724891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6060140062293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_452_1
  · norm_num [gridPoint]

theorem exp_5_453_0 : expNegUpper (15552444111901479545069 / 144893521275227648000 : ℝ) ≤ (969622378563 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1156529 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_453_1 : expNegUpper (7784947813565246393339 / 72446760637613824000 : ℝ) ≤ (5372477472477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_453 : rowCell 5 453 ≤ (1667353455631 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (969622378563 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5372477472477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_453_1
  · norm_num [gridPoint]

theorem exp_5_454_0 : expNegUpper (9684143404306111499549 / 90120683629949184000 : ℝ) ≤ (5372477299581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (578809 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_454_1 : expNegUpper (19390010313310666492217 / 180241367259898368000 : ℝ) ≤ (19049844960571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2317417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_454 : rowCell 5 454 ≤ (2956195295703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5372477299581 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19049844960571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_454_1
  · norm_num [gridPoint]

theorem exp_5_455_0 : expNegUpper (486294848228529863481737 / 4520392041768616448000 : ℝ) ≤ (4762461087851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2317417 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_455_1 : expNegUpper (60855003727766522069687 / 565049005221077056000 : ℝ) ≤ (3377095708963 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2319601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_455 : rowCell 5 455 ≤ (1310218015617 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4762461087851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3377095708963 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_455_1
  · norm_num [gridPoint]

theorem exp_5_456_0 : expNegUpper (61048601437619672267383 / 566846592543191104000 : ℝ) ≤ (8442739004141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2319601 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_456_1 : expNegUpper (97787218080296093174459 / 906954548069105766400 : ℝ) ≤ (14965820917583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2321789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_456 : rowCell 5 456 ≤ (580656333519 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8442739004141 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14965820917583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_456_1
  · norm_num [gridPoint]

theorem exp_5_457_0 : expNegUpper (98097814004985353135699 / 909835255445639270400 : ℝ) ≤ (2993164089011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2321789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_457_1 : expNegUpper (245519224781575088489443 / 2274588138614098176000 : ℝ) ≤ (13263346724749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2323981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_457 : rowCell 5 457 ≤ (411699246433 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2993164089011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13263346724749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_457_1
  · norm_num [gridPoint]

theorem exp_5_458_0 : expNegUpper (246297816896388336414547 / 2281801326208309504000 : ℝ) ≤ (663167315431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2323981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_458_1 : expNegUpper (493147117299479956606333 / 4563602652416619008000 : ℝ) ≤ (11753609934951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72693 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_458 : rowCell 5 458 ≤ (1824258925453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (663167315431 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11753609934951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_458_1
  · norm_num [gridPoint]

theorem exp_5_459_0 : expNegUpper (19788340511873829852797 / 183122074636431872000 : ℝ) ≤ (2350721913703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72693 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_459_1 : expNegUpper (4952621036028084514837 / 45780518659107968000 : ℝ) ≤ (10414901325413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18627 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_459 : rowCell 5 459 ≤ (1616547731407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2350721913703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10414901325413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_459_1
  · norm_num [gridPoint]

theorem exp_5_460_0 : expNegUpper (124206929257368158220013 / 1148130979427682432000 : ℝ) ≤ (5207450501379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (18627 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_460_1 : expNegUpper (497383418465474308340051 / 4592523917710729728000 : ℝ) ≤ (4613971916941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2330577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_460 : rowCell 5 460 ≤ (1432373893357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5207450501379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4613971916941 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_460_1
  · norm_num [gridPoint]

theorem exp_5_461_0 : expNegUpper (498953256482995979238539 / 4607018807816417792000 : ℝ) ≤ (2306985887449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2330577 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_461_1 : expNegUpper (9990221437596323478089 / 92140376156328355840 : ℝ) ≤ (817562161757 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166391 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_461 : rowCell 5 461 ≤ (63454180401 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2306985887449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (817562161757 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_461_1
  · norm_num [gridPoint]

theorem exp_5_462_0 : expNegUpper (10021702822995088642489 / 92430730724557219840 : ℝ) ≤ (8175621367461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1166391 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_462_1 : expNegUpper (501645073838172694905961 / 4621536536227860992000 : ℝ) ≤ (7242739113609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (145937 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_462 : rowCell 5 462 ≤ (1124320698713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8175621367461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7242739113609 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_462_1
  · norm_num [gridPoint]

theorem exp_5_463_0 : expNegUpper (503223381022086638266849 / 4636077102945059328000 : ℝ) ≤ (7242738893429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (145937 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_463_1 : expNegUpper (31486589645805157379603 / 289754818934066208000 : ℝ) ≤ (6415806800133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584301 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_463 : rowCell 5 463 ≤ (39839736933 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7242738893429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6415806800133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_463_1
  · norm_num [gridPoint]

theorem exp_5_464_0 : expNegUpper (1263419965230828110987 / 11626601269920032000 : ℝ) ≤ (801975825789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (584301 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_464_1 : expNegUpper (20237286534251371605463 / 186025620318720512000 : ℝ) ≤ (227314028711 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116971 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_464 : rowCell 5 464 ≤ (22056124049 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (801975825789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (227314028711 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_464_1
  · norm_num [gridPoint]

theorem exp_5_465_0 : expNegUpper (507518966352826897237367 / 4665226751296721408000 : ℝ) ≤ (177589079599 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116971 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_465_1 : expNegUpper (254042635450358328911903 / 2332613375648360704000 : ℝ) ≤ (2516621566493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (58541 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_465 : rowCell 5 465 ≤ (390713589449 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (177589079599 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2516621566493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_465_1
  · norm_num [gridPoint]

theorem exp_5_466_0 : expNegUpper (254838165897956121761807 / 2339917916465592576000 : ℝ) ≤ (201329719313 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (58541 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_466_1 : expNegUpper (102048953391703653572881 / 935967166586237030400 : ℝ) ≤ (4457552011217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2343863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_466 : rowCell 5 466 ≤ (173019324463 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201329719313 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4457552011217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_466_1
  · norm_num [gridPoint]

theorem exp_5_467_0 : expNegUpper (102368018482785185996521 / 938893550574280806400 : ℝ) ≤ (2228775939529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2343863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_467_1 : expNegUpper (128102665380506941746859 / 1173616938217851008000 : ℝ) ≤ (789481444703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234609 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_467 : rowCell 5 467 ≤ (612897169091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2228775939529 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (789481444703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_467_1
  · norm_num [gridPoint]

theorem exp_5_468_0 : expNegUpper (128502564549801650835851 / 1177280627779344512000 : ℝ) ≤ (394740710721 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234609 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_468_1 : expNegUpper (514582964583583801921963 / 4709122511117378048000 : ℝ) ≤ (1747690818907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14677 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_468 : rowCell 5 468 ≤ (67841855271 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (394740710721 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1747690818907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_468_1
  · norm_num [gridPoint]

theorem exp_5_469_0 : expNegUpper (20647473565763716413403 / 188952004306764288000 : ℝ) ≤ (1747690767733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14677 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_469_1 : expNegUpper (10335233722710500387941 / 94476002153382144000 : ℝ) ≤ (123795417963 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2350553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_469 : rowCell 5 469 ≤ (30035511841 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1747690767733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (123795417963 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_469_1
  · norm_num [gridPoint]

theorem exp_5_470_0 : expNegUpper (259184922620461748843341 / 2369250271263295744000 : ℝ) ≤ (386860669877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2350553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_470_1 : expNegUpper (518946836170190066141761 / 4738500542526591488000 : ℝ) ≤ (2740072283277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2352791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_470 : rowCell 5 470 ≤ (425490353621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (386860669877 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2740072283277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_470_1
  · norm_num [gridPoint]

theorem exp_5_471_0 : expNegUpper (520559286482037012127289 / 4753223815689830912000 : ℝ) ≤ (2740072204037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2352791 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_471_1 : expNegUpper (13028460616997939722129 / 118830595392245772800 : ℝ) ≤ (2425755771293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2355031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_471 : rowCell 5 471 ≤ (75339363427 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2740072204037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2425755771293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_471_1
  · norm_num [gridPoint]

theorem exp_5_472_0 : expNegUpper (13068879321494302509649 / 119199248178970636800 : ℝ) ≤ (2425755701577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2355031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_472_1 : expNegUpper (523336461657046234356311 / 4767969927158825472000 : ℝ) ≤ (536833858049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94291 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_472 : rowCell 5 472 ≤ (1302632477 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2425755701577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (536833858049 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_472_1
  · norm_num [gridPoint]

theorem exp_5_473_0 : expNegUpper (524957514366467409191759 / 4782738876933575168000 : ℝ) ≤ (2147335370861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94291 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_473_1 : expNegUpper (262770478546957324642139 / 2391369438466787584000 : ℝ) ≤ (1900730833329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2359523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_473 : rowCell 5 473 ≤ (59037724909 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2147335370861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1900730833329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_473_1
  · norm_num [gridPoint]

theorem exp_5_474_0 : expNegUpper (421733056795569268219 / 3838024532011264000 : ℝ) ≤ (475182694843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2359523 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_474_1 : expNegUpper (844403073572578368637 / 7676049064022528000 : ℝ) ≤ (1682323108321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1180887 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_474 : rowCell 5 474 ≤ (261279508641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (475182694843 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1682323108321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_474_1
  · norm_num [gridPoint]

theorem exp_5_475_0 : expNegUpper (529381602736093275360997 / 4812345291400339968000 : ℝ) ≤ (1682323060859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1180887 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_475_1 : expNegUpper (132492340829056343606729 / 1203086322850084992000 : ℝ) ≤ (1488903015577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_475 : rowCell 5 475 ≤ (231248654643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1682323060859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1488903015577 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_475_1
  · norm_num [gridPoint]

theorem exp_5_476_0 : expNegUpper (132900842395925281545641 / 1206795689023088768000 : ℝ) ≤ (148890297383 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2364029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_476_1 : expNegUpper (106438658817268995619943 / 965436551218471014400 : ℝ) ≤ (1317624810009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_476 : rowCell 5 476 ≤ (199857937 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (148890297383 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1317624810009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_476_1
  · norm_num [gridPoint]

theorem exp_5_477_0 : expNegUpper (106766326305924756893503 / 968408611818025062400 : ℝ) ≤ (1317624773291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2366287 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_477_1 : expNegUpper (267211861642779469072793 / 2421021529545062656000 : ℝ) ≤ (582982640593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2368549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_477 : rowCell 5 477 ≤ (181105618123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1317624773291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (582982640593 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_477_1
  · norm_num [gridPoint]

theorem exp_5_478_0 : expNegUpper (268033199283099948472457 / 2428463100196825344000 : ℝ) ≤ (1165965248893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2368549 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_478_1 : expNegUpper (536660660906205901293593 / 4856926200393650688000 : ℝ) ≤ (1031687382553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1185407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_478 : rowCell 5 478 ≤ (160254804339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1165965248893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1031687382553 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_478_1
  · norm_num [gridPoint]

theorem exp_5_479_0 : expNegUpper (458134196328313285399 / 4146240153193984000 : ℝ) ≤ (515843677077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1185407 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_479_1 : expNegUpper (14332556301612354103 / 129570004787312000 : ℝ) ≤ (228201985023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1186541 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_479 : rowCell 5 479 ≤ (17724292983 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (515843677077 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (228201985023 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_479_1
  · norm_num [gridPoint]

theorem sum_5_448_2 : blockSum (rowCell 5) 448 2 ≤ (1434822158969 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_448) (by simpa only [blockSum_one] using cell_5_449) (by norm_num)

theorem sum_5_450_2 : blockSum (rowCell 5) 450 2 ≤ (9026609687657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_450) (by simpa only [blockSum_one] using cell_5_451) (by norm_num)

theorem sum_5_448_4 : blockSum (rowCell 5) 448 4 ≤ (20505186959409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_448_2 sum_5_450_2 (by norm_num)

theorem sum_5_452_2 : blockSum (rowCell 5) 452 2 ≤ (3548042710079 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_452) (by simpa only [blockSum_one] using cell_5_453) (by norm_num)

theorem sum_5_454_2 : blockSum (rowCell 5) 454 2 ≤ (5576631326937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_454) (by simpa only [blockSum_one] using cell_5_455) (by norm_num)

theorem sum_5_452_4 : blockSum (rowCell 5) 452 4 ≤ (2534543349419 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_452_2 sum_5_454_2 (by norm_num)

theorem sum_5_448_8 : blockSum (rowCell 5) 448 8 ≤ (4147237963313 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_448_4 sum_5_452_4 (by norm_num)

theorem sum_5_456_2 : blockSum (rowCell 5) 456 2 ≤ (4381121566241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_456) (by simpa only [blockSum_one] using cell_5_457) (by norm_num)

theorem sum_5_458_2 : blockSum (rowCell 5) 458 2 ≤ (172040332843 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_458) (by simpa only [blockSum_one] using cell_5_459) (by norm_num)

theorem sum_5_456_4 : blockSum (rowCell 5) 456 4 ≤ (7821928223101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_456_2 sum_5_458_2 (by norm_num)

theorem sum_5_460_2 : blockSum (rowCell 5) 460 2 ≤ (2701457501377 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_460) (by simpa only [blockSum_one] using cell_5_461) (by norm_num)

theorem sum_5_462_2 : blockSum (rowCell 5) 462 2 ≤ (1060157061019 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_462) (by simpa only [blockSum_one] using cell_5_463) (by norm_num)

theorem sum_5_460_4 : blockSum (rowCell 5) 460 4 ≤ (964354324683 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_460_2 sum_5_462_2 (by norm_num)

theorem sum_5_456_8 : blockSum (rowCell 5) 456 8 ≤ (3160924961629 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_456_4 sum_5_460_4 (by norm_num)

theorem sum_5_448_16 : blockSum (rowCell 5) 448 16 ≤ (2291080177651 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_448_8 sum_5_456_8 (by norm_num)

theorem sum_5_464_2 : blockSum (rowCell 5) 464 2 ≤ (831836070429 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_464) (by simpa only [blockSum_one] using cell_5_465) (by norm_num)

theorem sum_5_466_2 : blockSum (rowCell 5) 466 2 ≤ (1304974466943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_466) (by simpa only [blockSum_one] using cell_5_467) (by norm_num)

theorem sum_5_464_4 : blockSum (rowCell 5) 464 4 ≤ (2968646607801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_464_2 sum_5_466_2 (by norm_num)

theorem sum_5_468_2 : blockSum (rowCell 5) 468 2 ≤ (127912878953 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_468) (by simpa only [blockSum_one] using cell_5_469) (by norm_num)

theorem sum_5_470_2 : blockSum (rowCell 5) 470 2 ≤ (200546792689 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_470) (by simpa only [blockSum_one] using cell_5_471) (by norm_num)

theorem sum_5_468_4 : blockSum (rowCell 5) 468 4 ≤ (91274510119 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_468_2 sum_5_470_2 (by norm_num)

theorem sum_5_464_8 : blockSum (rowCell 5) 464 8 ≤ (4794136810181 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_464_4 sum_5_468_4 (by norm_num)

theorem sum_5_472_2 : blockSum (rowCell 5) 472 2 ≤ (628662538657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_472) (by simpa only [blockSum_one] using cell_5_473) (by norm_num)

theorem sum_5_474_2 : blockSum (rowCell 5) 474 2 ≤ (123132040821 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_474) (by simpa only [blockSum_one] using cell_5_475) (by norm_num)

theorem sum_5_472_4 : blockSum (rowCell 5) 472 4 ≤ (1121190701941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_472_2 sum_5_474_2 (by norm_num)

theorem sum_5_476_2 : blockSum (rowCell 5) 476 2 ≤ (385760145611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_476) (by simpa only [blockSum_one] using cell_5_477) (by norm_num)

theorem sum_5_478_2 : blockSum (rowCell 5) 478 2 ≤ (302049148203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_478) (by simpa only [blockSum_one] using cell_5_479) (by norm_num)

theorem sum_5_476_4 : blockSum (rowCell 5) 476 4 ≤ (343904646907 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_476_2 sum_5_478_2 (by norm_num)

theorem sum_5_472_8 : blockSum (rowCell 5) 472 8 ≤ (361799999151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_472_4 sum_5_476_4 (by norm_num)

theorem sum_5_464_16 : blockSum (rowCell 5) 464 16 ≤ (412696050371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_464_8 sum_5_472_8 (by norm_num)

theorem sum_5_448_32 : blockSum (rowCell 5) 448 32 ≤ (13106185089739 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_448_16 sum_5_464_16 (by norm_num)

#print axioms sum_5_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
