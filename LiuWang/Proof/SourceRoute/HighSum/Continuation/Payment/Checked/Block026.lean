import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_320_0 : expNegUpper (3868838418653831441363 / 43572709073712392000 : ℝ) ≤ (1374743932702151696761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (400211 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_320_1 : expNegUpper (247917698467588945500111 / 2788653380717593088000 : ℝ) ≤ (1229209522701541826701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1001403 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_320 : rowCell 1 320 ≤ (189882625457469920987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1374743932702151696761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1229209522701541826701 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_320_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_320_1
  · norm_num [gridPoint]

theorem exp_1_321_0 : expNegUpper (248922074818709852628039 / 2799950908017562112000 : ℝ) ≤ (2458418875229158333229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1001403 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_321_1 : expNegUpper (24923576214413525773051 / 279995090801756211200 : ℝ) ≤ (137366400836185122383 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_321 : rowCell 1 321 ≤ (5305315858484755711 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2458418875229158333229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137366400836185122383 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_321_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_321_1
  · norm_num [gridPoint]

theorem exp_1_322_0 : expNegUpper (8341447904313301915577 / 93709042454109542400 : ℝ) ≤ (68683195702031600211 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2004559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_322_1 : expNegUpper (83519591812428561109687 / 937090424541095424000 : ℝ) ≤ (1964653506603721217053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2006317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_322 : rowCell 1 322 ≤ (151767194820376620517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68683195702031600211 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1964653506603721217053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_322_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_322_1
  · norm_num [gridPoint]

theorem exp_1_323_0 : expNegUpper (251569755718251473494109 / 2822614477534765568000 : ℝ) ≤ (982326686392988214213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2006317 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_323_1 : expNegUpper (62971687084844717256207 / 705653619383691392000 : ℝ) ≤ (877976050989269250609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_323 : rowCell 1 323 ≤ (135654946975654831207 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (982326686392988214213 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (877976050989269250609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_323_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_323_1
  · norm_num [gridPoint]

theorem exp_1_324_0 : expNegUpper (4046416649241691959 / 45343688316032000 : ℝ) ≤ (877975991667198472467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1004039 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_324_1 : expNegUpper (16206060213936221539 / 181374753264128000 : ℝ) ≤ (784604785195932141251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_324 : rowCell 1 324 ≤ (242473767947552394643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (877975991667198472467 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (784604785195932141251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_324_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_324_1
  · norm_num [gridPoint]

theorem exp_1_325_0 : expNegUpper (84745767233266842008849 / 948456466758329856000 : ℝ) ≤ (1569209465213239169809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2009843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_325_1 : expNegUpper (42426268823291351270711 / 474228233379164928000 : ℝ) ≤ (1402139316236073962557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_325 : rowCell 1 325 ≤ (10833671135722737349 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1569209465213239169809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1402139316236073962557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_325_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_325_1
  · norm_num [gridPoint]

theorem exp_1_326_0 : expNegUpper (127789274538587227995157 / 1428390559551867136000 : ℝ) ≤ (1402139223005662195281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2011611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_326_1 : expNegUpper (51180104924540290797213 / 571356223820746854400 : ℝ) ≤ (62634508601677224227 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2013383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_326 : rowCell 1 326 ≤ (19359254468454355663 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1402139223005662195281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (62634508601677224227 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_326_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_326_1
  · norm_num [gridPoint]

theorem exp_1_327_0 : expNegUpper (51384958540413236811573 / 573643135247646822400 : ℝ) ≤ (626345044701847936613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2013383 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_327_1 : expNegUpper (32156054485494018420167 / 358526959529779264000 : ℝ) ≤ (279755614330283609681 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_327 : rowCell 1 327 ≤ (86473704871332912219 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (626345044701847936613 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (279755614330283609681 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_327_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_327_1
  · norm_num [gridPoint]

theorem exp_1_328_0 : expNegUpper (10761501773617264873261 / 119986377986603712000 : ℝ) ≤ (559511192047520034413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2015159 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_328_1 : expNegUpper (86200452238612944826381 / 959891023892829696000 : ℝ) ≤ (499743219535525883871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1008469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_328 : rowCell 1 328 ≤ (154483566733042230009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (559511192047520034413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (499743219535525883871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_328_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_328_1
  · norm_num [gridPoint]

theorem exp_1_329_0 : expNegUpper (335009430533880801833 / 3730520394096128000 : ℝ) ≤ (999486374185999496743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1008469 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_329_1 : expNegUpper (167715675555290427141 / 1865260197048064000 : ℝ) ≤ (223150739097111197247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2018721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_329 : rowCell 1 329 ≤ (137972853909496415293 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (999486374185999496743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (223150739097111197247 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_329_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_329_1
  · norm_num [gridPoint]

theorem exp_1_330_0 : expNegUpper (10038215422509024006687 / 111640629902933248000 : ℝ) ≤ (892602898900916947633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2018721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_330_1 : expNegUpper (20101712850836521296817 / 223281259805866496000 : ℝ) ≤ (797045995268781952009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2020507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_330 : rowCell 1 330 ≤ (123210715406782799351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (892602898900916947633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (797045995268781952009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_330_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_330_1
  · norm_num [gridPoint]

theorem exp_1_331_0 : expNegUpper (87453309841194670649063 / 971394095944594944000 : ℝ) ≤ (12453842880331164621 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2020507 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_331_1 : expNegUpper (4378171275978355426307 / 48569704797229747200 : ℝ) ≤ (355813510022977674067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1011149 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_331 : rowCell 1 331 ≤ (110013788011477411113 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12453842880331164621 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (355813510022977674067 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_331_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_331_1
  · norm_num [gridPoint]

theorem exp_1_332_0 : expNegUpper (13186565213557221573481 / 146286551824853017600 : ℝ) ≤ (44476685933428726371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1011149 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_332_1 : expNegUpper (264063335596518454957011 / 2925731036497060352000 : ℝ) ≤ (31764044350974337593 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_332 : rowCell 1 332 ≤ (49108865703121581093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44476685933428726371 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31764044350974337593 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_332_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_332_1
  · norm_num [gridPoint]

theorem exp_1_333_0 : expNegUpper (265107735220254529470219 / 2937302623466091008000 : ℝ) ≤ (635280847065073523301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2024091 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_333_1 : expNegUpper (132720727083332405861729 / 1468651311733045504000 : ℝ) ≤ (567053182802119761141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2025889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_333 : rowCell 1 333 ≤ (21918819419973923277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (635280847065073523301 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (567053182802119761141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_333_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_333_1
  · norm_num [gridPoint]

theorem exp_1_334_0 : expNegUpper (1776594882421686351187 / 19659313658272512000 : ℝ) ≤ (35440821713680240337 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2025889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_334_1 : expNegUpper (3557661896819720568091 / 39318627316545024000 : ℝ) ≤ (101217769069283451707 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202769 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_334 : rowCell 1 334 ≤ (39127239131727440787 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35440821713680240337 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (101217769069283451707 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_334_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_334_1
  · norm_num [gridPoint]

theorem exp_1_335_0 : expNegUpper (267875805692478347822177 / 2960514312321417728000 : ℝ) ≤ (253044407007427541093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (202769 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_335_1 : expNegUpper (16763306867081237146011 / 185032144520088608000 : ℝ) ≤ (56452742443036916727 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1014747 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_335 : rowCell 1 335 ≤ (13967425718557679827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (253044407007427541093 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (56452742443036916727 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_335_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_335_1
  · norm_num [gridPoint]

theorem exp_1_336_0 : expNegUpper (16829216575016835101979 / 185759650887982112000 : ℝ) ≤ (225810955901761198431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1014747 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_336_1 : expNegUpper (10784250679778628545623 / 118886176568308551680 : ℝ) ≤ (201483235943099891193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_336 : rowCell 1 336 ≤ (31158676366452756273 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (225810955901761198431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (201483235943099891193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_336_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_336_1
  · norm_num [gridPoint]

theorem exp_1_337_0 : expNegUpper (3608856278386195211141 / 39784231391996866560 : ℝ) ≤ (50370805915923374231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2031303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_337_1 : expNegUpper (45167453936219241208181 / 497302892399960832000 : ℝ) ≤ (179754070021773426811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016557 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_337 : rowCell 1 337 ≤ (55600331946850587231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (50370805915923374231 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (179754070021773426811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_337_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_337_1
  · norm_num [gridPoint]

theorem exp_1_338_0 : expNegUpper (136033041360451416081487 / 1497751566448785664000 : ℝ) ≤ (359508118304085732357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1016557 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_338_1 : expNegUpper (272408289734187641890773 / 2995503132897571328000 : ℝ) ≤ (160348461757058329649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (203493 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_338 : rowCell 1 338 ≤ (49601162771100576941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (359508118304085732357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (160348461757058329649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_338_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_338_1
  · norm_num [gridPoint]

theorem exp_1_339_0 : expNegUpper (10938922428736903293717 / 120288469988045312000 : ℝ) ≤ (12827876170897327509 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (203493 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_339_1 : expNegUpper (2738169753374209442947 / 30072117497011328000 : ℝ) ≤ (143020215374846627847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2036749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_339 : rowCell 1 339 ≤ (11060957896346973549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12827876170897327509 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (143020215374846627847 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_339_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_339_1
  · norm_num [gridPoint]

theorem exp_1_340_0 : expNegUpper (22907097071988544842041 / 251578600400870784000 : ℝ) ≤ (286040413720638915513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2036749 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_340_1 : expNegUpper (91743596806451333729977 / 1006314401603483136000 : ℝ) ≤ (51019585312621703137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2038571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_340 : rowCell 1 340 ≤ (39460293952468461363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (286040413720638915513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51019585312621703137 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_340_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_340_1
  · norm_num [gridPoint]

theorem exp_1_341_0 : expNegUpper (276302405149561346176739 / 3030697498225521152000 : ℝ) ≤ (63774477873466208423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2038571 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_341_1 : expNegUpper (27664974497232545930553 / 303069749822552115200 : ℝ) ≤ (227474971173888175317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2040397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_341 : rowCell 1 341 ≤ (35189648165706821227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63774477873466208423 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (227474971173888175317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_341_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_341_1
  · norm_num [gridPoint]

theorem exp_1_342_0 : expNegUpper (27772479156785765328873 / 304247462994634803200 : ℝ) ≤ (227474957840328064253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2040397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_342_1 : expNegUpper (278073848988673965370561 / 3042474629946348032000 : ℝ) ≤ (50704652268958947337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2042227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_342 : rowCell 1 342 ≤ (15688696745701597223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (227474957840328064253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50704652268958947337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_342_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_342_1
  · norm_num [gridPoint]

theorem exp_1_343_0 : expNegUpper (7157752156694618106911 / 78314733332639232000 : ℝ) ≤ (202818597279291173473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2042227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_343_1 : expNegUpper (895843309169032583699 / 9789341666579904000 : ℝ) ≤ (11300815754172787919 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (102203 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_343 : rowCell 1 343 ≤ (13987382269687173419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (202818597279291173473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11300815754172787919 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_343_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_343_1
  · norm_num [gridPoint]

theorem exp_1_344_0 : expNegUpper (1402925213857986757741 / 15330487041526336000 : ℝ) ≤ (45203260407788838669 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (102203 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_344_1 : expNegUpper (11237501815234268330607 / 122643896332210688000 : ℝ) ≤ (161175806334224320929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_344 : rowCell 1 344 ≤ (24938134049241079841 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45203260407788838669 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (161175806334224320929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_344_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_344_1
  · norm_num [gridPoint]

theorem exp_1_345_0 : expNegUpper (282022927541718036153807 / 3077943054943359488000 : ℝ) ≤ (161175797103508441613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_345_1 : expNegUpper (141188578870684119276443 / 1538971527471679744000 : ℝ) ≤ (143654198499483536307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2047737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_345 : rowCell 1 345 ≤ (11114238575034674797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (161175797103508441613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (143654198499483536307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_345_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_345_1
  · norm_num [gridPoint]

theorem exp_1_346_0 : expNegUpper (47244333068965134452569 / 514968589981201152000 : ℝ) ≤ (8978386895962061911 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2047737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_346_1 : expNegUpper (18921463968974093580419 / 205987435992480460800 : ℝ) ≤ (128022260037772662607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_346 : rowCell 1 346 ≤ (4952722711380530393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8978386895962061911 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (128022260037772662607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_346_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_346_1
  · norm_num [gridPoint]

theorem exp_1_347_0 : expNegUpper (56982853076030861992417 / 620340572627361894400 : ℝ) ≤ (128022252817803063599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2049581 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_347_1 : expNegUpper (71317990188231212613609 / 775425715784202368000 : ℝ) ≤ (114077933563459018199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2051429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_347 : rowCell 1 347 ≤ (441354077570195823 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (128022252817803063599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (114077933563459018199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_347_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_347_1
  · norm_num [gridPoint]

theorem exp_1_348_0 : expNegUpper (71591934608286798155721 / 778404256173041792000 : ℝ) ≤ (57038963589542492603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2051429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_348_1 : expNegUpper (286727171388647225526403 / 3113617024692167168000 : ℝ) ≤ (101640568137506268587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12833 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_348 : rowCell 1 348 ≤ (15730386488071470227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57038963589542492603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (101640568137506268587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_348_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_348_1
  · norm_num [gridPoint]

theorem exp_1_349_0 : expNegUpper (153507428034724320761 / 1666962146428416000 : ℝ) ≤ (6352535155787331983 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (12833 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_349_1 : expNegUpper (76850027049097913507 / 833481073214208000 : ℝ) ≤ (22637168515066699477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1027567 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_349 : rowCell 1 349 ≤ (14014611799452066339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6352535155787331983 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22637168515066699477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_349_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_349_1
  · norm_num [gridPoint]

theorem exp_1_350_0 : expNegUpper (144645171384187841551561 / 1568756931360073984000 : ℝ) ≤ (90548669069681383083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1027567 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_350_1 : expNegUpper (289653260881673347558041 / 3137513862720147968000 : ℝ) ≤ (5041119411916397907 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (64281 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_350 : rowCell 1 350 ≤ (12484537607243679811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90548669069681383083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5041119411916397907 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_350_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_350_1
  · norm_num [gridPoint]

theorem exp_1_351_0 : expNegUpper (290759494035288584380689 / 3149496539192771072000 : ℝ) ≤ (80657906179000279451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (64281 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_351_1 : expNegUpper (1819525998272839924849 / 19684353369954819200 : ℝ) ≤ (14367856543011081637 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1029427 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_351 : rowCell 1 351 ≤ (5560116011673843873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80657906179000279451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14367856543011081637 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_351_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_351_1
  · norm_num [gridPoint]

theorem sum_1_320_2 : blockSum (rowCell 1) 320 2 ≤ (359652732928982103739 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_320) (by simpa only [blockSum_one] using cell_1_321) (by norm_num)

theorem sum_1_322_2 : blockSum (rowCell 1) 322 2 ≤ (71855535449007862931 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_322) (by simpa only [blockSum_one] using cell_1_323) (by norm_num)

theorem sum_1_320_4 : blockSum (rowCell 1) 320 4 ≤ (647074874725013555463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_320_2 sum_1_322_2 (by norm_num)

theorem sum_1_324_2 : blockSum (rowCell 1) 324 2 ≤ (459147190662007141623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_324) (by simpa only [blockSum_one] using cell_1_325) (by norm_num)

theorem sum_1_326_2 : blockSum (rowCell 1) 326 2 ≤ (91634988606802345267 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_326) (by simpa only [blockSum_one] using cell_1_327) (by norm_num)

theorem sum_1_324_4 : blockSum (rowCell 1) 324 4 ≤ (825687145089216522691 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_324_2 sum_1_326_2 (by norm_num)

theorem sum_1_320_8 : blockSum (rowCell 1) 320 8 ≤ (2119836894539243633617 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_320_4 sum_1_324_4 (by norm_num)

theorem sum_1_328_2 : blockSum (rowCell 1) 328 2 ≤ (146228210321269322651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_328) (by simpa only [blockSum_one] using cell_1_329) (by norm_num)

theorem sum_1_330_2 : blockSum (rowCell 1) 330 2 ≤ (7288265731820631577 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_330) (by simpa only [blockSum_one] using cell_1_331) (by norm_num)

theorem sum_1_328_4 : blockSum (rowCell 1) 328 4 ≤ (262840462030399427883 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_328_2 sum_1_330_2 (by norm_num)

theorem sum_1_332_2 : blockSum (rowCell 1) 332 2 ≤ (92946504543069427647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_332) (by simpa only [blockSum_one] using cell_1_333) (by norm_num)

theorem sum_1_334_2 : blockSum (rowCell 1) 334 2 ≤ (148091606856243280709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_334) (by simpa only [blockSum_one] using cell_1_335) (by norm_num)

theorem sum_1_332_4 : blockSum (rowCell 1) 332 4 ≤ (333984615942382136003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_332_2 sum_1_334_2 (by norm_num)

theorem sum_1_328_8 : blockSum (rowCell 1) 328 8 ≤ (859665540003180991769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_328_4 sum_1_332_4 (by norm_num)

theorem sum_1_320_16 : blockSum (rowCell 1) 320 16 ≤ (1489751217271212312693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_320_8 sum_1_328_8 (by norm_num)

theorem sum_1_336_2 : blockSum (rowCell 1) 336 2 ≤ (117917684679756099777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_336) (by simpa only [blockSum_one] using cell_1_337) (by norm_num)

theorem sum_1_338_2 : blockSum (rowCell 1) 338 2 ≤ (93844994356488471137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_338) (by simpa only [blockSum_one] using cell_1_339) (by norm_num)

theorem sum_1_336_4 : blockSum (rowCell 1) 336 4 ≤ (105881339518122285457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_336_2 sum_1_338_2 (by norm_num)

theorem sum_1_340_2 : blockSum (rowCell 1) 340 2 ≤ (7464994211817528259 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_340) (by simpa only [blockSum_one] using cell_1_341) (by norm_num)

theorem sum_1_342_2 : blockSum (rowCell 1) 342 2 ≤ (14838039507694385321 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_342) (by simpa only [blockSum_one] using cell_1_343) (by norm_num)

theorem sum_1_340_4 : blockSum (rowCell 1) 340 4 ≤ (67001050074476411937 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_340_2 sum_1_342_2 (by norm_num)

theorem sum_1_336_8 : blockSum (rowCell 1) 336 8 ≤ (86441194796299348697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_336_4 sum_1_340_4 (by norm_num)

theorem sum_1_344_2 : blockSum (rowCell 1) 344 2 ≤ (9433322239862085887 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_344) (by simpa only [blockSum_one] using cell_1_345) (by norm_num)

theorem sum_1_346_2 : blockSum (rowCell 1) 346 2 ≤ (9366263487082488623 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_346) (by simpa only [blockSum_one] using cell_1_347) (by norm_num)

theorem sum_1_344_4 : blockSum (rowCell 1) 344 4 ≤ (84631665147640383927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_344_2 sum_1_346_2 (by norm_num)

theorem sum_1_348_2 : blockSum (rowCell 1) 348 2 ≤ (14872499143761768283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_348) (by simpa only [blockSum_one] using cell_1_349) (by norm_num)

theorem sum_1_350_2 : blockSum (rowCell 1) 350 2 ≤ (23604769630591367557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_350) (by simpa only [blockSum_one] using cell_1_351) (by norm_num)

theorem sum_1_348_4 : blockSum (rowCell 1) 348 4 ≤ (53349767918114904123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_348_2 sum_1_350_2 (by norm_num)

theorem sum_1_344_8 : blockSum (rowCell 1) 344 8 ≤ (2759628661315105761 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_344_4 sum_1_348_4 (by norm_num)

theorem sum_1_336_16 : blockSum (rowCell 1) 336 16 ≤ (241873106125476341419 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_336_8 sum_1_344_8 (by norm_num)

theorem sum_1_320_32 : blockSum (rowCell 1) 320 32 ≤ (54113260106146520441 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_320_16 sum_1_336_16 (by norm_num)

#print axioms sum_1_320_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
