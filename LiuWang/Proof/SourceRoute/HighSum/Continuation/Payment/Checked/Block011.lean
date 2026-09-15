import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_352_0 : expNegUpper (200276935856587363881 / 2195487537479964800 : ℝ) ≤ (120825579501446160029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1019717 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_352_1 : expNegUpper (32085831773557713737079 / 351278005996794368000 : ℝ) ≤ (107355443922941901151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020659 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_352 : rowCell 0 352 ≤ (1663916523449461027 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (120825579501446160029 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (107355443922941901151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_352_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_352_1
  · norm_num [gridPoint]

theorem exp_0_353_0 : expNegUpper (289871159270385156656039 / 3173530407055282688000 : ℝ) ≤ (214710877169162858351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1020659 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_353_1 : expNegUpper (145123305917773006630359 / 1586765203527641344000 : ℝ) ≤ (190754036101728402091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1021603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_353 : rowCell 0 353 ≤ (3695858220074550941 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (214710877169162858351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (190754036101728402091 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_353_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_353_1
  · norm_num [gridPoint]

theorem exp_0_354_0 : expNegUpper (5826975938958915382239 / 63711631968903424000 : ℝ) ≤ (190754026687986344027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1021603 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_354_1 : expNegUpper (11669040283220536463437 / 127423263937806848000 : ℝ) ≤ (84726286275325243759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_354 : rowCell 0 354 ≤ (1313329441979895061 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (190754026687986344027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (84726286275325243759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_354_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_354_1
  · norm_num [gridPoint]

theorem exp_0_355_0 : expNegUpper (32536856739834032009493 / 355295069793423872000 : ℝ) ≤ (42363141062807835721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2045097 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_355_1 : expNegUpper (8144741158035007370511 / 88823767448355968000 : ℝ) ≤ (150514248993935633253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2046991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_355 : rowCell 0 355 ≤ (4666453498404270171 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (42363141062807835721 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (150514248993935633253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_355_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_355_1
  · norm_num [gridPoint]

theorem exp_0_356_0 : expNegUpper (73579977598601340076391 / 802438124035553408000 : ℝ) ≤ (37628560419396983381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2046991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_356_1 : expNegUpper (58940129130825044249439 / 641950499228442726400 : ℝ) ≤ (133678738520076452819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2048889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_356 : rowCell 0 356 ≤ (1295225465352770837 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37628560419396983381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (133678738520076452819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_356_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_356_1
  · norm_num [gridPoint]

theorem exp_0_357_0 : expNegUpper (59162681229596326500279 / 644374440489873510400 : ℝ) ≤ (133678732070927021701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2048889 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_357_1 : expNegUpper (148097954483723463020693 / 1610936101224683776000 : ℝ) ≤ (14839272148616812901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (205079 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_357 : rowCell 0 357 ≤ (9202358851241757777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (133678732070927021701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14839272148616812901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_357_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_357_1
  · norm_num [gridPoint]

theorem exp_0_358_0 : expNegUpper (16517344883976319522333 / 179667485947904256000 : ℝ) ≤ (118714171504696714491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (205079 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_358_1 : expNegUpper (33077386846840447383337 / 359334971895808512000 : ℝ) ≤ (105414077098704868509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (410539 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_358 : rowCell 0 358 ≤ (16343633253383398051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (118714171504696714491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (105414077098704868509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_358_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_358_1
  · norm_num [gridPoint]

theorem exp_0_359_0 : expNegUpper (11952653027100814549457 / 129847205199237632000 : ℝ) ≤ (21082814417818883159 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (410539 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_359_1 : expNegUpper (1496011868044075846011 / 16230900649904704000 : ℝ) ≤ (46797285666435969179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2054603 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_359 : rowCell 0 359 ≤ (1813986134394732621 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21082814417818883159 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (46797285666435969179 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_359_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_359_1
  · norm_num [gridPoint]

theorem exp_0_360_0 : expNegUpper (1210991005799032726749 / 13138582061311936000 : ℝ) ≤ (93594566918206237007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2054603 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_360_1 : expNegUpper (9700438545856096807321 / 105108656490495488000 : ℝ) ≤ (83091955442581732873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_360 : rowCell 0 360 ≤ (2576827990469218457 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (93594566918206237007 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (83091955442581732873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_360_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_360_1
  · norm_num [gridPoint]

theorem exp_0_361_0 : expNegUpper (33537838798425739513671 / 363397712303948288000 : ℝ) ≤ (2077298788813545091 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1028257 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_361_1 : expNegUpper (671622567893498152563 / 7267954246078965760 : ℝ) ≤ (36880246922675636223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2058429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_361 : rowCell 0 361 ≤ (5718910620266637639 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2077298788813545091 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (36880246922675636223 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_361_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_361_1
  · norm_num [gridPoint]

theorem exp_0_362_0 : expNegUpper (6067213498257472572667 / 65656266171429283840 : ℝ) ≤ (2950419616715495033 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2058429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_362_1 : expNegUpper (303752065492759318810461 / 3282813308571464192000 : ℝ) ≤ (13094092571651860543 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2060347 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_362 : rowCell 0 362 ≤ (5076423101603099919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2950419616715495033 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13094092571651860543 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_362_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_362_1
  · norm_num [gridPoint]

theorem exp_0_363_0 : expNegUpper (304886156611624681993749 / 3295070044713148928000 : ℝ) ≤ (32735229919311868897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2060347 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_363_1 : expNegUpper (76319833683983274556837 / 823767511178287232000 : ℝ) ≤ (58106405072679253167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_363 : rowCell 0 363 ≤ (180226720308435657 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (32735229919311868897 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58106405072679253167 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_363_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_363_1
  · norm_num [gridPoint]

theorem exp_0_364_0 : expNegUpper (340463338082692736037 / 3674832910178432000 : ℝ) ≤ (2324256096502865431 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2062269 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_364_1 : expNegUpper (1363608770106374016147 / 14699331640713728000 : ℝ) ≤ (51565572454131943197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1032097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_364 : rowCell 0 364 ≤ (7997378940694944283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2324256096502865431 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51565572454131943197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_364_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_364_1
  · norm_num [gridPoint]

theorem exp_0_365_0 : expNegUpper (307953227893608616681067 / 3319652031913783808000 : ℝ) ≤ (51565570110943962777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1032097 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_365_1 : expNegUpper (154174995549550565878353 / 1659826015956891904000 : ℝ) ≤ (45756537947208228479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033061 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_365 : rowCell 0 365 ≤ (7096815557431916283 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51565570110943962777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45756537947208228479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_365_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_365_1
  · norm_num [gridPoint]

theorem exp_0_366_0 : expNegUpper (154747418730759395733057 / 1665988641486366976000 : ℝ) ≤ (45756535883356375903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1033061 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_366_1 : expNegUpper (61978679640754535865461 / 666395456594546790400 : ℝ) ≤ (5074744688838847391 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_366 : rowCell 0 366 ≤ (3148523621205267839 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45756535883356375903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5074744688838847391 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_366_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_366_1
  · norm_num [gridPoint]

theorem exp_0_367_0 : expNegUpper (6912040954899836300389 / 74318341607498649600 : ℝ) ≤ (40597955693046860253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1034027 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_367_1 : expNegUpper (2162793087363107243569 / 23224481752343328000 : ℝ) ≤ (7203493285640745539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2069989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_367 : rowCell 0 367 ≤ (1117373083049980987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40597955693046860253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7203493285640745539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_367_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_367_1
  · norm_num [gridPoint]

theorem exp_0_368_0 : expNegUpper (19537140900804299347769 / 209793518750493728000 : ℝ) ≤ (36017464827494149069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2069989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_368_1 : expNegUpper (312996420220984069725663 / 3356696300007899648000 : ℝ) ≤ (3993836932174292807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_368 : rowCell 0 368 ≤ (4956299313118074757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36017464827494149069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3993836932174292807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_368_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_368_1
  · norm_num [gridPoint]

theorem exp_0_369_0 : expNegUpper (12566083271239436253423 / 134763602639364608000 : ℝ) ≤ (31950694047860193423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2071927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_369_1 : expNegUpper (6291121102364024120231 / 67381801319682304000 : ℝ) ≤ (5668078783833272661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2073869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_369 : rowCell 0 369 ≤ (4396480302329921893 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31950694047860193423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5668078783833272661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_369_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_369_1
  · norm_num [gridPoint]

theorem exp_0_370_0 : expNegUpper (17539740837065701697799 / 187861481681449216000 : ℝ) ≤ (28340392678077237831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2073869 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_370_1 : expNegUpper (35124568807141944295629 / 375722963362898432000 : ℝ) ≤ (2513564820245450251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1037907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_370 : rowCell 0 370 ≤ (3899520945888853109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28340392678077237831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2513564820245450251 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_370_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_370_1
  · norm_num [gridPoint]

theorem exp_0_371_0 : expNegUpper (317284024263797608967789 / 3393946112853811712000 : ℝ) ≤ (3141955888721227251 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1037907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_371_1 : expNegUpper (15884581132577579720103 / 169697305642690585600 : ℝ) ≤ (22291185391375616729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2077763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_371 : rowCell 0 371 ≤ (3458407236028350349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3141955888721227251 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22291185391375616729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_371_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_371_1
  · norm_num [gridPoint]

theorem exp_0_372_0 : expNegUpper (15942907968158474414343 / 170320419687364633600 : ℝ) ≤ (5572796107356976959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2077763 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_372_1 : expNegUpper (319267575272362139964811 / 3406408393747292672000 : ℝ) ≤ (308855512832173323 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415943 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_372 : rowCell 0 372 ≤ (1533451285374047371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5572796107356976959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (308855512832173323 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_372_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_372_1
  · norm_num [gridPoint]

theorem exp_0_373_0 : expNegUpper (35604194484181879471851 / 379877056994058752000 : ℝ) ≤ (19766751974474395953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (415943 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_373_1 : expNegUpper (17824943728835987893221 / 189938528497029376000 : ℝ) ≤ (17526565354031284607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (208167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_373 : rowCell 0 373 ≤ (679865551327355389 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19766751974474395953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17526565354031284607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_373_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_373_1
  · norm_num [gridPoint]

theorem exp_0_374_0 : expNegUpper (257618245791630829261 / 2745121176361216000 : ℝ) ≤ (8763282304341147487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (208167 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_374_1 : expNegUpper (515897389094315467953 / 5490242352722432000 : ℝ) ≤ (15538813042988564311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083629 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_374 : rowCell 0 374 ≤ (2411157045535072983 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8763282304341147487 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15538813042988564311 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_374_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_374_1
  · norm_num [gridPoint]

theorem exp_0_375_0 : expNegUpper (323613340001212999004697 / 3443932266262266368000 : ℝ) ≤ (15538812386976743877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2083629 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_375_1 : expNegUpper (40503528557424867858977 / 430491533282783296000 : ℝ) ≤ (13775222643263535259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2085591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_375 : rowCell 0 375 ≤ (2137605771233468637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15538812386976743877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13775222643263535259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_375_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_375_1
  · norm_num [gridPoint]

theorem exp_0_376_0 : expNegUpper (4516796647708318739737 / 48006748616371776000 : ℝ) ≤ (13775222065926797731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2085591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_376_1 : expNegUpper (7236135065283150111347 / 76810797786194841600 : ℝ) ≤ (6105333563520583401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (521889 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_376 : rowCell 0 376 ≤ (1894914386648545781 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13775222065926797731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6105333563520583401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_376_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_376_1
  · norm_num [gridPoint]

theorem exp_0_377_0 : expNegUpper (65362174626647006814883 / 693812474560204902400 : ℝ) ≤ (2442133323796830419 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (521889 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_377_1 : expNegUpper (163614713305657125308043 / 1734531186400512256000 : ℝ) ≤ (2705704497648148849 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (83581 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_377 : rowCell 0 377 ≤ (102516015129191 / 61035156250000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2442133323796830419 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2705704497648148849 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_377_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_377_1
  · norm_num [gridPoint]

theorem exp_0_378_0 : expNegUpper (164208946744129950086907 / 1740830841764518144000 : ℝ) ≤ (10822817543536895499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (83581 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_378_1 : expNegUpper (328838284472455076417293 / 3481661683529036288000 : ℝ) ≤ (1198979462666153113 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2091497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_378 : rowCell 0 378 ≤ (297730971181132437 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10822817543536895499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1198979462666153113 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_378_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_378_1
  · norm_num [gridPoint]

theorem exp_0_379_0 : expNegUpper (1466801909744054196837 / 15530150366945792000 : ℝ) ≤ (9591835307981228513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2091497 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_379_1 : expNegUpper (367169623903892087937 / 3882537591736448000 : ℝ) ≤ (1700018826877120413 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (65421 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_379 : rowCell 0 379 ≤ (1319279749405247663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9591835307981228513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1700018826877120413 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_379_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_379_1
  · norm_num [gridPoint]

theorem exp_0_380_0 : expNegUpper (82912122934507640786753 / 876732204975581312000 : ℝ) ≤ (8500093788319896629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (65421 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_380_1 : expNegUpper (332072567726796305523171 / 3506928819902325248000 : ℝ) ≤ (7531935296029359769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2095451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_380 : rowCell 0 380 ≤ (1169069964606878247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8500093788319896629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7531935296029359769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_380_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_380_1
  · norm_num [gridPoint]

theorem exp_0_381_0 : expNegUpper (333272089617453653478939 / 3519596645547602432000 : ℝ) ≤ (1506386998317173869 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2095451 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_381_1 : expNegUpper (33369801310467400228597 / 351959664554760243200 : ℝ) ≤ (6673451031124761173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097433 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_381 : rowCell 0 381 ≤ (1035869511427563957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1506386998317173869 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6673451031124761173 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_381_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_381_1
  · norm_num [gridPoint]

theorem exp_0_382_0 : expNegUpper (3721124814700223466813 / 39247636772207052800 : ℝ) ≤ (1334690152663602109 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2097433 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_382_1 : expNegUpper (37258778626608290684529 / 392476367722070528000 : ℝ) ≤ (1182457753801353643 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1049709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_382 : rowCell 0 382 ≤ (917763434197483941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1334690152663602109 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1182457753801353643 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_382_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_382_1
  · norm_num [gridPoint]

theorem exp_0_383_0 : expNegUpper (336535932847068585478769 / 3545000811755422208000 : ℝ) ≤ (5912288533445851323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1049709 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_383_1 : expNegUpper (2632543447840131202161 / 27695318841839236000 : ℝ) ≤ (5237478680989046591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2101407 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_383 : rowCell 0 383 ≤ (32522041705822979 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5912288533445851323 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5237478680989046591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_383_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_383_1
  · norm_num [gridPoint]

theorem sum_0_352_2 : blockSum (rowCell 0) 352 2 ≤ (15711299057396407017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_352) (by simpa only [blockSum_one] using cell_0_353) (by norm_num)

theorem sum_0_354_2 : blockSum (rowCell 0) 354 2 ≤ (1983954253264770083 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_354) (by simpa only [blockSum_one] using cell_0_355) (by norm_num)

theorem sum_0_352_4 : blockSum (rowCell 0) 352 4 ≤ (112444052561204880143 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_352_2 sum_0_354_2 (by norm_num)

theorem sum_0_356_2 : blockSum (rowCell 0) 356 2 ≤ (19564162574063924473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_356) (by simpa only [blockSum_one] using cell_0_357) (by norm_num)

theorem sum_0_358_2 : blockSum (rowCell 0) 358 2 ≤ (30855522328541259019 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_358) (by simpa only [blockSum_one] using cell_0_359) (by norm_num)

theorem sum_0_356_4 : blockSum (rowCell 0) 356 4 ≤ (13996769495333821593 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_356_2 sum_0_358_2 (by norm_num)

theorem sum_0_352_8 : blockSum (rowCell 0) 352 8 ≤ (45606975009468497027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_352_4 sum_0_356_4 (by norm_num)

theorem sum_0_360_2 : blockSum (rowCell 0) 360 2 ≤ (24321961192879367563 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_360) (by simpa only [blockSum_one] using cell_0_361) (by norm_num)

theorem sum_0_362_2 : blockSum (rowCell 0) 362 2 ≤ (598880694332124459 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_362) (by simpa only [blockSum_one] using cell_0_363) (by norm_num)

theorem sum_0_360_4 : blockSum (rowCell 0) 360 4 ≤ (43486143411507350251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_360_2 sum_0_362_2 (by norm_num)

theorem sum_0_364_2 : blockSum (rowCell 0) 364 2 ≤ (7547097249063430283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_364) (by simpa only [blockSum_one] using cell_0_365) (by norm_num)

theorem sum_0_366_2 : blockSum (rowCell 0) 366 2 ≤ (11883912657660440613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_366) (by simpa only [blockSum_one] using cell_0_367) (by norm_num)

theorem sum_0_364_4 : blockSum (rowCell 0) 364 4 ≤ (26978107155787301179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_364_2 sum_0_366_2 (by norm_num)

theorem sum_0_360_8 : blockSum (rowCell 0) 360 8 ≤ (7046425056729465143 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_360_4 sum_0_364_4 (by norm_num)

theorem sum_0_352_16 : blockSum (rowCell 0) 352 16 ≤ (126446075302584319769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_352_8 sum_0_360_8 (by norm_num)

theorem sum_0_368_2 : blockSum (rowCell 0) 368 2 ≤ (187055592308959933 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_368) (by simpa only [blockSum_one] using cell_0_369) (by norm_num)

theorem sum_0_370_2 : blockSum (rowCell 0) 370 2 ≤ (3678964090958601729 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_370) (by simpa only [blockSum_one] using cell_0_371) (by norm_num)

theorem sum_0_368_4 : blockSum (rowCell 0) 368 4 ≤ (4177676949341300027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_368_2 sum_0_370_2 (by norm_num)

theorem sum_0_372_2 : blockSum (rowCell 0) 372 2 ≤ (2893182388028758149 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_372) (by simpa only [blockSum_one] using cell_0_373) (by norm_num)

theorem sum_0_374_2 : blockSum (rowCell 0) 374 2 ≤ (227438140838427081 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_374) (by simpa only [blockSum_one] using cell_0_375) (by norm_num)

theorem sum_0_372_4 : blockSum (rowCell 0) 372 4 ≤ (5167563796413028959 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_372_2 sum_0_374_2 (by norm_num)

theorem sum_0_368_8 : blockSum (rowCell 0) 368 8 ≤ (13522917695095629013 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_368_4 sum_0_372_4 (by norm_num)

theorem sum_0_376_2 : blockSum (rowCell 0) 376 2 ≤ (28596294228201689 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_376) (by simpa only [blockSum_one] using cell_0_377) (by norm_num)

theorem sum_0_378_2 : blockSum (rowCell 0) 378 2 ≤ (350991825663863731 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_378) (by simpa only [blockSum_one] using cell_0_379) (by norm_num)

theorem sum_0_376_4 : blockSum (rowCell 0) 376 4 ≤ (6382471383836120973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_376_2 sum_0_378_2 (by norm_num)

theorem sum_0_380_2 : blockSum (rowCell 0) 380 2 ≤ (551234869008610551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_380) (by simpa only [blockSum_one] using cell_0_381) (by norm_num)

theorem sum_0_382_2 : blockSum (rowCell 0) 382 2 ≤ (108175904802691151 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_382) (by simpa only [blockSum_one] using cell_0_383) (by norm_num)

theorem sum_0_380_4 : blockSum (rowCell 0) 380 4 ≤ (196787697643875031 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_380_2 sum_0_382_2 (by norm_num)

theorem sum_0_376_8 : blockSum (rowCell 0) 376 8 ≤ (10318225336713621593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_376_4 sum_0_380_4 (by norm_num)

theorem sum_0_368_16 : blockSum (rowCell 0) 368 16 ≤ (37364060726904879619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_368_8 sum_0_376_8 (by norm_num)

theorem sum_0_352_32 : blockSum (rowCell 0) 352 32 ≤ (290256211332073519157 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_352_16 sum_0_368_16 (by norm_num)

#print axioms sum_0_352_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
